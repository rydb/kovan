//! A transaction that loads a variable twice, with another transaction
//! committing it in between, sees one value of it: the second load is
//! validated like the first, so the attempt retries rather than commit two.

use kovan_stm::Stm;
use std::sync::{Arc, mpsc};
use std::thread;

#[test]
fn a_reread_sees_the_value_the_first_read_saw() {
    let stm = Arc::new(Stm::new());
    let x = Arc::new(stm.tvar(0i64));
    let (go_tx, go_rx) = mpsc::channel::<()>();
    let (done_tx, done_rx) = mpsc::channel::<()>();
    let writer = {
        let (stm, x) = (stm.clone(), x.clone());
        thread::spawn(move || {
            go_rx.recv().unwrap();
            stm.atomically(|tx| tx.store(&x, 1));
            done_tx.send(()).unwrap();
        })
    };
    let mut first = true;
    let mut attempts = 0;
    // A read-only transaction; between its two loads another one commits x.
    let (a, b) = stm.atomically(|tx| {
        attempts += 1;
        let a = tx.load(&x)?;
        if first {
            first = false;
            go_tx.send(()).unwrap();
            done_rx.recv().unwrap();
        }
        let b = tx.load(&x)?;
        Ok((a, b))
    });
    writer.join().unwrap();
    assert_eq!(a, b, "one committed transaction saw two values of x");
    assert_eq!((a, b), (1, 1), "the retry reads the committed value");
    assert_eq!(attempts, 2, "the attempt that met the commit retried once");
}

#[test]
fn a_reread_of_an_update_transaction_sees_one_value() {
    let stm = Arc::new(Stm::new());
    let x = Arc::new(stm.tvar(0i64));
    let y = Arc::new(stm.tvar(0i64));
    let (go_tx, go_rx) = mpsc::channel::<()>();
    let (done_tx, done_rx) = mpsc::channel::<()>();
    let writer = {
        let (stm, x) = (stm.clone(), x.clone());
        thread::spawn(move || {
            go_rx.recv().unwrap();
            stm.atomically(|tx| tx.store(&x, 7));
            done_tx.send(()).unwrap();
        })
    };
    let mut first = true;
    let seen = stm.atomically(|tx| {
        let a = tx.load(&x)?;
        if first {
            first = false;
            go_tx.send(()).unwrap();
            done_rx.recv().unwrap();
        }
        let b = tx.load(&x)?;
        tx.store(&y, a + b)?;
        Ok((a, b))
    });
    writer.join().unwrap();
    assert_eq!(seen, (7, 7));
    assert_eq!(stm.atomically(|tx| tx.load(&y)), 14);
}
