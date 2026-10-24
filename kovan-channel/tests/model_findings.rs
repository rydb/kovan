//! The lost wakeups and hangs the TLA+ model (`proofs/tla/channel`) found on
//! 0.1.22 that a test can drive step by step: an async operation dropped, or
//! completed on its fast path, while its wait list entry is queued; a bounded
//! send with every receiver gone; and `select!` once every channel is
//! disconnected. (The windows inside one blocking call are in
//! `tests/shuttle_channel.rs`.)

use kovan_channel::signal::Signal;
use kovan_channel::{bounded, select, unbounded};
use std::future::Future;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering::SeqCst};
use std::task::{Context, Poll, Wake, Waker};
use std::thread;
use std::time::{Duration, Instant};

/// A waker that records whether it was woken.
struct Flag(AtomicBool);

impl Wake for Flag {
    fn wake(self: Arc<Self>) {
        self.0.store(true, SeqCst);
    }
}

fn flag() -> (Arc<Flag>, Waker) {
    let f = Arc::new(Flag(AtomicBool::new(false)));
    (f.clone(), Waker::from(f))
}

fn poll<F: Future + Unpin>(f: &mut F, waker: &Waker) -> Poll<F::Output> {
    std::pin::Pin::new(f).poll(&mut Context::from_waker(waker))
}

#[test]
fn a_dropped_recv_async_does_not_take_a_wakeup() {
    let (s, r) = unbounded::<u32>();
    {
        let (_woken, w) = flag();
        let mut dropped = Box::pin(r.recv_async());
        assert!(poll(&mut dropped, &w).is_pending());
    }
    let (woken, w) = flag();
    let mut waiting = Box::pin(r.recv_async());
    assert!(poll(&mut waiting, &w).is_pending());
    s.send(7);
    assert!(
        woken.0.load(SeqCst),
        "the send's wakeup went to the dropped future's entry"
    );
    assert_eq!(poll(&mut waiting, &w), Poll::Ready(Some(7)));
}

#[test]
fn a_recv_async_done_on_its_fast_path_does_not_keep_its_entry() {
    let (s, r) = unbounded::<u32>();
    let (first_woken, w0) = flag();
    let mut first = Box::pin(r.recv_async());
    assert!(poll(&mut first, &w0).is_pending());
    let (_second_woken, w1) = flag();
    let mut second = Box::pin(r.recv_async());
    assert!(poll(&mut second, &w1).is_pending());
    // The send wakes the first; the second, polled again before it, takes
    // the value on its fast path, its own entry still queued.
    s.send(1);
    assert!(first_woken.0.swap(false, SeqCst));
    assert_eq!(poll(&mut second, &w1), Poll::Ready(Some(1)));
    // The first finds nothing and waits again.
    assert!(poll(&mut first, &w0).is_pending());
    s.send(2);
    assert!(
        first_woken.0.load(SeqCst),
        "the second send's wakeup went to the finished future's entry"
    );
    assert_eq!(poll(&mut first, &w0), Poll::Ready(Some(2)));
}

#[test]
fn a_dropped_send_async_does_not_take_a_wakeup() {
    let (s, r) = bounded::<u32>(1);
    s.send(0);
    {
        let (_woken, w) = flag();
        let mut dropped = Box::pin(s.send_async(1));
        assert!(poll(&mut dropped, &w).is_pending());
    }
    let (woken, w) = flag();
    let mut waiting = Box::pin(s.send_async(2));
    assert!(poll(&mut waiting, &w).is_pending());
    assert_eq!(r.try_recv(), Some(0));
    assert!(
        woken.0.load(SeqCst),
        "the freed slot's wakeup went to the dropped future's entry"
    );
    assert_eq!(poll(&mut waiting, &w), Poll::Ready(()));
    assert_eq!(r.try_recv(), Some(2));
}

/// Runs `f` on a thread and fails if it does not return by a deadline.
fn returns_in_time(what: &str, f: impl FnOnce() + Send + 'static) {
    let done = Arc::new(AtomicBool::new(false));
    let t = {
        let done = done.clone();
        thread::spawn(move || {
            f();
            done.store(true, SeqCst);
        })
    };
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut pause = Duration::from_micros(50);
    while !done.load(SeqCst) {
        assert!(Instant::now() < deadline, "{what} never returned");
        thread::sleep(pause);
        pause = (pause * 2).min(Duration::from_millis(20));
    }
    t.join().unwrap();
}

#[test]
fn a_bounded_send_returns_once_every_receiver_is_gone() {
    let (s, r) = bounded::<u32>(1);
    s.send(1);
    let other = r.clone();
    drop(r);
    assert!(!s.is_disconnected());
    drop(other);
    assert!(s.is_disconnected());
    returns_in_time("a send on a full channel with no receiver", move || {
        s.send(2)
    });
}

#[test]
fn a_waiting_bounded_send_returns_when_the_last_receiver_goes() {
    let (s, r) = bounded::<u32>(1);
    s.send(1);
    let waiting = thread::spawn(move || s.send(2));
    drop(r);
    returns_in_time("the waiting send", move || waiting.join().unwrap());
}

#[test]
fn select_runs_its_disconnected_arm_once_every_channel_is_gone() {
    let (s1, r1) = unbounded::<u32>();
    let (s2, r2) = bounded::<u32>(1);
    drop(s1);
    drop(s2);
    let got = select! {
        v = r1 => Some(v),
        w = r2 => Some(w);
        disconnected => None,
    };
    assert_eq!(got, None);
}

#[test]
fn select_takes_what_is_left_before_its_disconnected_arm() {
    let (s1, r1) = unbounded::<u32>();
    s1.send(5);
    drop(s1);
    let got = select! {
        v = r1 => Some(v);
        disconnected => None,
    };
    assert_eq!(got, Some(5));
}

#[test]
fn a_waiting_select_ends_when_its_channels_disconnect() {
    let (s1, r1) = unbounded::<u32>();
    let (s2, r2) = unbounded::<u32>();
    let waiting = thread::spawn(move || {
        select! {
            v = r1 => Some(v),
            w = r2 => Some(w);
            disconnected => None,
        }
    });
    drop(s1);
    drop(s2);
    returns_in_time("a select over channels that disconnected", move || {
        assert_eq!(waiting.join().unwrap(), None);
    });
}

#[test]
#[should_panic(expected = "every channel is disconnected and empty")]
fn select_without_a_disconnected_arm_panics_instead_of_waiting_for_good() {
    let (s1, r1) = unbounded::<u32>();
    drop(s1);
    let _: u32 = select! {
        v = r1 => v,
    };
}

#[test]
fn a_signal_another_channel_notified_can_be_registered() {
    // `select!` registers its one signal on its channels one after another,
    // and a send on the first can notify it before it reaches the second
    // (`CH_select_assert`): `register_signal` used to `debug_assert!`
    // against that. The entry is stale, and a later send skips it.
    let (s1, r1) = unbounded::<u32>();
    let (s2, r2) = bounded::<u32>(1);
    let sig = Arc::new(Signal::new());
    r1.register_signal(sig.clone());
    s1.send(1);
    assert!(sig.is_notified());
    r2.register_signal(sig.clone());
    assert!(!sig.cancel(), "a notifier woke it first");
    s2.send(2);
    assert_eq!((r1.try_recv(), r2.try_recv()), (Some(1), Some(2)));
}
