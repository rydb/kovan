//! The magazine cache behind the `recycle` feature: the memory of freed
//! nodes is kept per thread and per size class, so the next node of that size
//! takes it back without a call into the global allocator.
//!
//! # What it is
//!
//! The magazine layer of Bonwick and Adams ("Magazines and Vmem", USENIX
//! 2001), per thread instead of per CPU. Node sizes are rounded up to one of
//! [`CLASS_SIZES`] (multiples of 16 bytes up to 1 KiB, every block aligned to
//! 16); larger nodes, or nodes aligned to more than 16, bypass the cache.
//!
//! - A magazine holds up to [`ROUNDS`] free blocks of one class.
//! - Each thread keeps two magazines per class, `loaded` and `previous`.
//!   Freeing pushes on `loaded` and allocating pops from it, with no atomic
//!   operation. When `loaded` is full (on a free) or empty (on an
//!   allocation), the thread swaps it with `previous` if that helps; only
//!   when neither does it goes to the depot.
//! - The depot, one per class, holds full magazines and empty ones, each in
//!   a bounded lock-free ring of [`DEPOT_SLOTS`] slots. A thread with two
//!   full magazines hands one to the depot and takes an empty one; a thread
//!   with two empty ones hands one back and takes a full one.
//! - Under them, the slab layer (`slab.rs`): a thread that finds no full
//!   magazine in the depot fills its loaded one with about 2 KiB of blocks
//!   carved from chunks it owns, of 8 KiB each, taken from the global
//!   allocator one chunk at a time; a full magazine the depot has no room
//!   for gives its blocks back to their chunks, and a chunk goes back to the
//!   global allocator once all its blocks are back.
//! - A thread's magazines go back to the depot when the thread exits (or,
//!   where the depot is full, their blocks to their chunks), and its chunks
//!   are freed by whichever thread gives back each one's last block.
//!
//! So a thread that frees about as much as it allocates of a class touches
//! only its own magazines; a producer that allocates and a consumer that
//! frees trade one magazine of [`ROUNDS`] blocks through the depot per
//! [`ROUNDS`] nodes.
//!
//! # Memory bound
//!
//! Per class, the magazines hold at most `2 * ROUNDS` blocks per thread plus
//! `DEPOT_SLOTS * ROUNDS` blocks in the depot, and the magazines that carry
//! them (264 bytes each on 64-bit targets): two per thread that used the
//! class, and at most `2 * DEPOT_SLOTS` in the depot. With 32 rounds and 16
//! slots that is 64 blocks per thread and 512 in the depot per class: for
//! 64-byte nodes, 4 KiB per thread and 32 KiB in the depot. The depot's
//! rings are statics: 20 classes, two rings of 16 slots of two words each,
//! plus two ticket words per ring.
//!
//! The slab layer holds the chunks that still have a block out (live, or in
//! a magazine), plus at most one empty chunk per thread and class. A chunk's
//! free blocks wait for its owner to hand them out again, so a chunk with
//! one long-lived node keeps its 8 KiB: as with any slab allocator, scattered
//! long-lived nodes can keep more memory than they use.
//!
//! # Progress
//!
//! The magazine paths take no lock and make no atomic operation. A ring's
//! push and pop are lock-free: each retries only after another thread moved
//! the ring on, and a full ring's push and an empty ring's pop answer at
//! once. A slot a thread is still filling reads as empty (to a pop) and full
//! (to a push) until it is published, so an operation never waits for another
//! thread: the cache then goes to the slab layer. The slab layer's paths are
//! lock-free too (see `slab.rs`); only a new chunk or a new magazine calls the
//! global allocator.
//!
//! # Ordering
//!
//! A magazine handed to the depot is published with a release store of its
//! slot's sequence word and taken with an acquire load of it: everything the
//! handing thread wrote before (the blocks it put in the magazine, and what it
//! wrote into those blocks while they were nodes) happens before everything
//! the taking thread does with them after.
//!
//! The protocol is model-checked in `proofs/tla/magazine/Magazine.tla`, and
//! the rings' sequence arithmetic and the classes are proved in
//! `proofs/lean/Kovan/Magazine.lean`.

use alloc::boxed::Box;
use core::cell::UnsafeCell;
use core::mem;
use core::ptr;
use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use crate::atomic::AtomicUsize;

// vertexia: as for kovan's handle in `guard.rs`, shuttle's cooperative threads
// share one OS thread, so the per-thread magazines must be shuttle's
// thread-locals under the `shuttle` feature.
#[cfg(feature = "shuttle")]
use shuttle::thread_local;

/// The free blocks one magazine holds.
pub(crate) const ROUNDS: usize = 32;

/// The magazines each of a class's two depot rings holds (a power of two).
pub(crate) const DEPOT_SLOTS: usize = 16;

/// The block sizes of the classes, in bytes: a node takes the smallest that
/// fits it. Every size is a multiple of [`CLASS_ALIGN`], so every block is
/// aligned to it.
pub(crate) const CLASS_SIZES: [usize; 20] = [
    16, 32, 48, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 384, 448, 512, 640, 768, 896, 1024,
];

/// The alignment of every block.
pub(crate) const CLASS_ALIGN: usize = 16;

mod slab;
use slab::SlabClass;

/// The bytes of blocks an allocation takes from the slab layer when the depot
/// has no full magazine: the blocks beyond the one it hands out wait in its
/// loaded magazine, so the allocations after it take the fast path.
const REFILL_BYTES: usize = 2048;

/// The fresh blocks a refill of `class` takes: about [`REFILL_BYTES`] of
/// them, at least one and at most a magazine.
const fn refill_count(class: usize) -> usize {
    let n = REFILL_BYTES / CLASS_SIZES[class];
    if n < 1 {
        1
    } else if n > ROUNDS {
        ROUNDS
    } else {
        n
    }
}

/// What [`class_of`] answers for a node the cache does not take.
pub(crate) const NO_CLASS: usize = usize::MAX;

/// The class of a node of `size` bytes aligned to `align`: the index of the
/// smallest class that fits it, or [`NO_CLASS`] for a zero-sized node, a node
/// aligned to more than [`CLASS_ALIGN`] or one larger than the largest class.
pub(crate) const fn class_of(size: usize, align: usize) -> usize {
    if size == 0 || align > CLASS_ALIGN {
        return NO_CLASS;
    }
    let mut i = 0;
    while i < CLASS_SIZES.len() {
        if size <= CLASS_SIZES[i] {
            return i;
        }
        i += 1;
    }
    NO_CLASS
}

/// Up to [`ROUNDS`] free blocks of one class.
pub(crate) struct Magazine {
    len: usize,
    rounds: [*mut u8; ROUNDS],
}

impl Magazine {
    /// An empty magazine, from the global allocator (the cache keeps empty
    /// magazines in the depot, so this runs only while the cache grows).
    #[cold]
    fn new_empty() -> *mut Magazine {
        Box::into_raw(Box::new(Magazine {
            len: 0,
            rounds: [ptr::null_mut(); ROUNDS],
        }))
    }

    /// Gives every block of the magazine back to its chunk, leaving the
    /// magazine empty. `mine` is the calling thread's slab of the class and
    /// owner id, when it still has them.
    ///
    /// # Safety
    ///
    /// `magazine` is valid and owned by the caller, and holds free blocks of
    /// the slab layer.
    unsafe fn release_rounds(magazine: *mut Magazine, mut mine: Option<(&mut SlabClass, usize)>) {
        // SAFETY: the caller owns the magazine.
        let m = unsafe { &mut *magazine };
        for &block in &m.rounds[..m.len] {
            let mine = mine.as_mut().map(|(slab, owner)| (&mut **slab, *owner));
            // SAFETY: a magazine holds only free blocks of the slab layer.
            unsafe { slab::release(block, mine) };
        }
        m.len = 0;
    }

    /// How many blocks the magazine at `magazine` holds; a null pointer holds
    /// none.
    fn len_of(magazine: *const Magazine) -> usize {
        // SAFETY: a non-null magazine pointer of a thread's pair or of the
        // depot is valid and owned by whoever reads it here.
        unsafe { magazine.as_ref() }.map_or(0, |m| m.len)
    }
}

/// One slot of a [`Ring`]: the magazine it holds and its turn word.
struct Slot {
    turn: AtomicUsize,
    magazine: AtomicUsize,
}

/// A bounded lock-free ring of magazines: the sequence-numbered ring of
/// Vyukov's bounded multi-producer multi-consumer queue.
///
/// A push takes a ticket `t` from `push_at` and fills slot `t % DEPOT_SLOTS`,
/// a pop takes one from `pop_at` and empties that slot. The tickets that land
/// on one slot are one turn apart; the turn of ticket `t` is
/// `t - t % DEPOT_SLOTS`. A slot's word says where it stands: equal to the
/// turn, it waits for that turn's push; one more, it holds that turn's
/// magazine, waiting for its pop; one turn more, it waits for the next turn's
/// push. (Vyukov's sequence word is this word plus the slot's index; keeping
/// the index out lets every slot start with the same word.) Tickets and words
/// count modulo the word size and are compared by their wrapped difference,
/// which is exact while they are fewer than half the word's range apart: they
/// are never more than `DEPOT_SLOTS` apart.
pub(crate) struct Ring {
    slots: [Slot; DEPOT_SLOTS],
    push_at: AtomicUsize,
    pop_at: AtomicUsize,
}

/// The turn of ticket `ticket`.
#[inline]
fn turn_of(ticket: usize) -> usize {
    ticket - ticket % DEPOT_SLOTS
}

impl Ring {
    /// An empty ring whose tickets start at `START`, a multiple of
    /// `DEPOT_SLOTS` (tests start it near the end of the ticket range).
    pub(crate) const fn starting_at<const START: usize>() -> Ring {
        const { assert!(START.is_multiple_of(DEPOT_SLOTS)) };
        Ring {
            slots: [const {
                Slot {
                    turn: AtomicUsize::new(START),
                    magazine: AtomicUsize::new(0),
                }
            }; DEPOT_SLOTS],
            push_at: AtomicUsize::new(START),
            pop_at: AtomicUsize::new(START),
        }
    }

    /// An empty ring.
    pub(crate) const fn new() -> Ring {
        Ring::starting_at::<0>()
    }

    /// Hands `magazine` to the ring, or gives it back when every slot is
    /// taken.
    pub(crate) fn push(&self, magazine: *mut Magazine) -> Result<(), *mut Magazine> {
        let mut ticket = self.push_at.load(Relaxed);
        loop {
            let slot = &self.slots[ticket % DEPOT_SLOTS];
            let turn = turn_of(ticket);
            match (slot.turn.load(Acquire).wrapping_sub(turn) as isize).signum() {
                0 => match self.push_at.compare_exchange_weak(
                    ticket,
                    ticket.wrapping_add(1),
                    Relaxed,
                    Relaxed,
                ) {
                    Ok(_) => {
                        slot.magazine.store(magazine as usize, Relaxed);
                        slot.turn.store(turn.wrapping_add(1), Release);
                        return Ok(());
                    }
                    Err(now) => ticket = now,
                },
                // The slot still holds the magazine of the turn before: full.
                -1 => return Err(magazine),
                // Another push took this ticket: move on to the current one.
                _ => ticket = self.push_at.load(Relaxed),
            }
        }
    }

    /// Takes a magazine from the ring, or `None` when no slot holds one.
    pub(crate) fn pop(&self) -> Option<*mut Magazine> {
        let mut ticket = self.pop_at.load(Relaxed);
        loop {
            let slot = &self.slots[ticket % DEPOT_SLOTS];
            let turn = turn_of(ticket);
            match (slot.turn.load(Acquire).wrapping_sub(turn.wrapping_add(1)) as isize).signum() {
                0 => match self.pop_at.compare_exchange_weak(
                    ticket,
                    ticket.wrapping_add(1),
                    Relaxed,
                    Relaxed,
                ) {
                    Ok(_) => {
                        let magazine = slot.magazine.load(Relaxed) as *mut Magazine;
                        slot.turn.store(turn.wrapping_add(DEPOT_SLOTS), Release);
                        return Some(magazine);
                    }
                    Err(now) => ticket = now,
                },
                // No push has filled this turn yet: empty.
                -1 => return None,
                // Another pop took this ticket: move on to the current one.
                _ => ticket = self.pop_at.load(Relaxed),
            }
        }
    }
}

/// The depot of one class: its full and its empty magazines.
struct Depot {
    full: Ring,
    empty: Ring,
}

impl Depot {
    const fn new() -> Depot {
        Depot {
            full: Ring::new(),
            empty: Ring::new(),
        }
    }

    /// An empty magazine: one the depot keeps, or a new one.
    fn take_empty(&self) -> *mut Magazine {
        self.empty.pop().unwrap_or_else(Magazine::new_empty)
    }

    /// Keeps an empty magazine for a later [`take_empty`](Self::take_empty),
    /// or frees it when the depot keeps as many as it can.
    fn give_empty(&self, magazine: *mut Magazine) {
        if let Err(magazine) = self.empty.push(magazine) {
            // SAFETY: made by `Magazine::new_empty`, and the caller gave it up.
            drop(unsafe { Box::from_raw(magazine) });
        }
    }

    /// Takes back a magazine a thread no longer uses: a magazine with blocks
    /// to the full ring (its blocks back to their chunks when the ring has no
    /// room), an empty one to the empty ring.
    fn give_back(&self, magazine: *mut Magazine, mine: Option<(&mut SlabClass, usize)>) {
        if Magazine::len_of(magazine) > 0 {
            match self.full.push(magazine) {
                Ok(()) => return,
                // SAFETY: the caller gave the magazine up; it holds free
                // blocks of the slab layer.
                Err(magazine) => unsafe { Magazine::release_rounds(magazine, mine) },
            }
        }
        self.give_empty(magazine);
    }
}

/// The depots, one per class.
#[cfg(not(feature = "shuttle"))]
struct Depots([Depot; CLASS_SIZES.len()]);

#[cfg(not(feature = "shuttle"))]
static DEPOTS: Depots = Depots([const { Depot::new() }; CLASS_SIZES.len()]);

// vertexia: under shuttle, a plain static of shuttle atomics would be shared by
// the tests cargo runs on parallel OS threads, which shuttle's atomics do not
// allow; shuttle's `lazy_static!` gives each execution its own depots and drops
// them when the execution ends (without freeing the magazines they still hold:
// shuttle's atomics cannot be read once the execution is over, so a shuttle
// test build leaks one execution's leftovers; only such builds use this path).
// Shuttle's atomics carry a vector clock each,
// so the depots are built one by one on the heap: all of them at once would
// not fit the stack of a shuttle task.
#[cfg(feature = "shuttle")]
struct Depots(Box<[Depot]>);

#[cfg(feature = "shuttle")]
shuttle::lazy_static! {
    static ref DEPOTS: Depots =
        Depots((0..CLASS_SIZES.len()).map(|_| Depot::new()).collect());
}

impl core::ops::Deref for Depots {
    type Target = [Depot];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// One thread's two magazines of one class.
///
/// Invariants: `loaded` is null only while `previous` is; `previous` is null,
/// empty or full.
struct Pair {
    loaded: *mut Magazine,
    previous: *mut Magazine,
}

impl Pair {
    /// The fast path: a block from `loaded`.
    #[inline]
    fn pop(&mut self) -> Option<*mut u8> {
        // SAFETY: the pair's magazines are this thread's alone.
        if let Some(m) = unsafe { self.loaded.as_mut() }
            && m.len > 0
        {
            m.len -= 1;
            return Some(m.rounds[m.len]);
        }
        None
    }

    /// `loaded` is null or empty: take `previous` if it is full, else a full
    /// magazine from the depot, else refill `loaded` from the slab layer.
    #[cold]
    fn pop_slow(
        &mut self,
        depot: &Depot,
        class: usize,
        slab: &mut SlabClass,
        owner: usize,
    ) -> *mut u8 {
        if Magazine::len_of(self.previous) > 0 {
            mem::swap(&mut self.loaded, &mut self.previous);
        } else if let Some(full) = depot.full.pop() {
            let drained = mem::replace(&mut self.loaded, full);
            if !drained.is_null() {
                depot.give_empty(drained);
            }
        } else {
            return self.refill(depot, class, slab, owner);
        }
        // SAFETY: `loaded` is now a full magazine or one from the depot's full
        // ring, which holds at least one block, and it is this thread's.
        let m = unsafe { &mut *self.loaded };
        m.len -= 1;
        m.rounds[m.len]
    }

    /// The depot has no full magazine: hands out a block from the slab layer,
    /// and puts [`refill_count`] minus one more in `loaded` (null or empty),
    /// loading an empty magazine first if it is null.
    #[cold]
    fn refill(
        &mut self,
        depot: &Depot,
        class: usize,
        slab: &mut SlabClass,
        owner: usize,
    ) -> *mut u8 {
        if self.loaded.is_null() {
            self.loaded = depot.take_empty();
        }
        // SAFETY: `loaded` is an empty magazine of this thread's.
        let m = unsafe { &mut *self.loaded };
        // The first block carved is handed out and the rest pop in the order
        // they were carved, so nodes allocated one after another lie at rising
        // addresses, which the prefetcher streams; popped in reverse, a lookup
        // over 100,000 keys inserted in order met three times the cache misses.
        let first = slab.alloc(class, owner);
        let rest = refill_count(class) - 1;
        for i in (0..rest).rev() {
            m.rounds[i] = slab.alloc(class, owner);
        }
        m.len = rest;
        first
    }

    /// The fast path: `block` pushed on `loaded`. Answers whether it was.
    #[inline]
    fn push(&mut self, block: *mut u8) -> bool {
        // SAFETY: the pair's magazines are this thread's alone.
        if let Some(m) = unsafe { self.loaded.as_mut() }
            && m.len < ROUNDS
        {
            m.rounds[m.len] = block;
            m.len += 1;
            return true;
        }
        false
    }

    /// `loaded` is null or full: take `previous` if it is empty; otherwise
    /// hand a full `previous` to the depot (or, with no room there, give its
    /// blocks back to their chunks and take it), make `loaded` the new
    /// `previous` and load an empty magazine.
    #[cold]
    fn push_slow(&mut self, depot: &Depot, block: *mut u8, slab: &mut SlabClass, owner: usize) {
        if !self.previous.is_null() && Magazine::len_of(self.previous) == 0 {
            mem::swap(&mut self.loaded, &mut self.previous);
        } else {
            let mut kept = false;
            if !self.previous.is_null() {
                match depot.full.push(self.previous) {
                    Ok(()) => self.previous = ptr::null_mut(),
                    Err(full) => {
                        // SAFETY: the pair's magazine, holding free blocks of
                        // the slab layer.
                        unsafe { Magazine::release_rounds(full, Some((slab, owner))) };
                        mem::swap(&mut self.loaded, &mut self.previous);
                        kept = true;
                    }
                }
            }
            if !kept {
                self.previous = self.loaded;
                self.loaded = depot.take_empty();
            }
        }
        // SAFETY: `loaded` is now an empty magazine of this thread's.
        let m = unsafe { &mut *self.loaded };
        m.rounds[m.len] = block;
        m.len += 1;
    }
}

/// One thread's magazines and chunks, for every class.
struct ThreadCache {
    pairs: [Pair; CLASS_SIZES.len()],
    slabs: [SlabClass; CLASS_SIZES.len()],
    /// The thread's owner id for its chunks; 0 until it makes its first.
    owner: usize,
}

impl ThreadCache {
    fn owner(&mut self) -> usize {
        if self.owner == 0 {
            self.owner = slab::new_owner();
        }
        self.owner
    }

    #[inline]
    fn alloc(&mut self, class: usize) -> *mut u8 {
        match self.pairs[class].pop() {
            Some(block) => block,
            None => self.alloc_slow(class),
        }
    }

    #[cold]
    fn alloc_slow(&mut self, class: usize) -> *mut u8 {
        let owner = self.owner();
        self.pairs[class].pop_slow(&DEPOTS[class], class, &mut self.slabs[class], owner)
    }

    #[inline]
    fn free(&mut self, class: usize, block: *mut u8) {
        if !self.pairs[class].push(block) {
            self.free_slow(class, block);
        }
    }

    #[cold]
    fn free_slow(&mut self, class: usize, block: *mut u8) {
        let owner = self.owner();
        self.pairs[class].push_slow(&DEPOTS[class], block, &mut self.slabs[class], owner);
    }
}

impl Drop for ThreadCache {
    fn drop(&mut self) {
        let owner = self.owner();
        for (class, (pair, slab)) in self.pairs.iter_mut().zip(self.slabs.iter_mut()).enumerate() {
            for magazine in [pair.loaded, pair.previous] {
                if !magazine.is_null() {
                    DEPOTS[class].give_back(magazine, Some((&mut *slab, owner)));
                }
            }
            pair.loaded = ptr::null_mut();
            pair.previous = ptr::null_mut();
            slab.orphan();
        }
    }
}

thread_local! {
    // An `UnsafeCell`, not a `RefCell`: every access below is one call that
    // neither runs user code nor calls back into the cache (the depot's rings,
    // the slab layer and the global allocator are all it reaches), so no two
    // accesses of one thread overlap.
    static CACHE: UnsafeCell<ThreadCache> = const {
        UnsafeCell::new(ThreadCache {
            pairs: [const { Pair { loaded: ptr::null_mut(), previous: ptr::null_mut() } };
                CLASS_SIZES.len()],
            slabs: [const { SlabClass::new() }; CLASS_SIZES.len()],
            owner: 0,
        })
    };
}

/// A block of `class`: from this thread's magazines, the depot, or the slab
/// layer.
#[inline]
pub(crate) fn alloc_block(class: usize) -> *mut u8 {
    // SAFETY: the cache is this thread's, and the access does not overlap
    // another (see `CACHE`).
    let cached = CACHE.try_with(|cache| unsafe { (*cache.get()).alloc(class) });
    // The thread's cache is gone (thread exit): a block of a chunk of its own.
    cached.unwrap_or_else(|_| slab::lone_block(class))
}

/// Gives a free block of `class` back to the cache.
///
/// # Safety
///
/// `block` came from [`alloc_block`] for the same class, holds no live
/// value, and nothing uses it any more.
#[inline]
pub(crate) unsafe fn free_block(block: *mut u8, class: usize) {
    // SAFETY: the cache is this thread's, and the access does not overlap
    // another (see `CACHE`).
    let cached = CACHE.try_with(|cache| unsafe { (*cache.get()).free(class, block) });
    if cached.is_err() {
        // The thread's cache is gone (thread exit): back to its chunk.
        // SAFETY: the caller's contract.
        unsafe { slab::release_remote(block) };
    }
}

#[cfg(test)]
mod tests;
