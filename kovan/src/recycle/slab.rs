//! The slab layer under the magazine cache: blocks are carved from chunks
//! taken from the global allocator one chunk at a time, and a chunk goes back
//! once all its blocks are free. So a run of allocations the magazines cannot
//! serve costs one allocator call per chunk, not one per node.
//!
//! # Chunks and owners
//!
//! A chunk is [`CHUNK_BYTES`] aligned to its size, so a block finds its chunk
//! by masking its address. It starts with a header and holds blocks of one
//! class. The thread that made it owns it: only the owner carves its blocks,
//! keeps its free list and frees it, with no atomic operation on those paths.
//!
//! A block comes back to the slab layer when the magazines have no room for it
//! (the depot is full) or a thread's cache goes away. The owner puts a block
//! of its own chunk on the chunk's free list. Any other thread pushes it on the
//! owner's inbox for the block's class, one lock-free list per owner and class;
//! the owner drains it when it has no chunk with a block to take, before it
//! would make a new chunk. When a chunk's last block comes back, the owner
//! frees it (keeping one empty chunk per class, so alternating runs do not
//! allocate and free a chunk each time).
//!
//! # A thread's exit
//!
//! The exiting owner drains its inboxes, writes into each chunk the count of
//! its blocks still out, then closes each inbox, counting down for the blocks
//! pushed in between. From then on, a thread giving back a block of such a
//! chunk finds the inbox closed and counts down instead; whoever brings the
//! count to zero frees the chunk. An inbox is freed when its owner and every
//! chunk that names it are gone.
//!
//! # Lifetimes
//!
//! A thread giving back a block holds a block of the chunk, so the chunk (and
//! the inbox it names) cannot be freed until that block is counted back. Its
//! one push, or its one count-down, is the last thing it does with either: the
//! owner may free both right after.
//!
//! The protocol is model-checked in `proofs/tla/slab/Slab.tla`, and the chunk
//! geometry is proved in `proofs/lean/Kovan/Magazine.lean`.

use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use alloc::boxed::Box;
use core::cell::UnsafeCell;
use core::ptr;
use core::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};

use super::{CLASS_ALIGN, CLASS_SIZES};
use crate::atomic::AtomicUsize;

/// The bytes of a chunk, a power of two: chunks are aligned to it.
pub(crate) const CHUNK_BYTES: usize = 8192;

/// The bytes the header takes at the start of a chunk, rounded up to
/// [`CLASS_ALIGN`]: blocks start after it, aligned.
pub(crate) const HEADER_BYTES: usize = size_of::<Chunk>().div_ceil(CLASS_ALIGN) * CLASS_ALIGN;

/// The low bit of an inbox's word: the owner has exited.
const CLOSED: usize = 1;

const _: () = {
    assert!(CHUNK_BYTES.is_power_of_two());
    assert!(capacity(CLASS_SIZES.len() - 1) >= 2);
};

/// The blocks a chunk of `class` holds.
pub(crate) const fn capacity(class: usize) -> usize {
    (CHUNK_BYTES - HEADER_BYTES) / CLASS_SIZES[class]
}

/// The chunk a block of the slab layer lies in.
fn chunk_of(block: *mut u8) -> *mut Chunk {
    block.map_addr(|a| a & !(CHUNK_BYTES - 1)).cast()
}

/// A free block's first word: the next block of a list it is on.
///
/// # Safety
///
/// `block` is a free block of at least a word, aligned to [`CLASS_ALIGN`].
unsafe fn set_next(block: *mut u8, next: *mut u8) {
    // SAFETY: the caller's contract.
    unsafe { block.cast::<*mut u8>().write(next) }
}

/// # Safety
///
/// As for [`set_next`], and the block's first word was written by it.
unsafe fn next_of(block: *mut u8) -> *mut u8 {
    // SAFETY: the caller's contract.
    unsafe { block.cast::<*mut u8>().read() }
}

/// An owner's inbox for one class: blocks other threads gave back, linked
/// through their first word, with [`CLOSED`] set once the owner exited.
struct Inbox {
    blocks: AtomicUsize,
    /// The owner (until it exits) and every chunk that names this inbox.
    refs: AtomicUsize,
}

/// Drops one reference to `inbox`, freeing it with the last.
///
/// # Safety
///
/// The caller holds a reference to a live inbox and gives it up here.
unsafe fn release_inbox(inbox: *mut Inbox) {
    // SAFETY: the caller's reference keeps the inbox alive until here.
    if unsafe { &*inbox }.refs.fetch_sub(1, AcqRel) == 1 {
        // SAFETY: no reference is left: nothing reaches the inbox.
        drop(unsafe { Box::from_raw(inbox) });
    }
}

/// The header at the start of a chunk.
///
/// Split in two so that no reference covers both: other threads read the
/// shared part (fixed fields and the count) while the owner changes its own,
/// and a reference to the whole header would claim the bytes another thread
/// is using.
#[repr(C)]
struct Chunk {
    shared: ChunkShared,
    own: UnsafeCell<ChunkOwn>,
}

/// What any thread reads of a chunk.
struct ChunkShared {
    /// Once the owner exited: the blocks not yet given back.
    outstanding: AtomicUsize,
    /// The owner's inbox for this class (fixed for the chunk's life).
    inbox: *mut Inbox,
    /// The owner's id (fixed for the chunk's life; ids are never reused).
    owner: usize,
    /// The block size's class.
    class: usize,
}

/// What only the owner reads and writes.
struct ChunkOwn {
    /// Blocks carved so far.
    carved: usize,
    /// Blocks out of the chunk: carved or taken from `local`, and not back.
    used: usize,
    /// Blocks back from the owner or from the inbox, ready to hand out again.
    local: *mut u8,
    /// The owner's list of all its chunks of this class.
    prev_all: *mut Chunk,
    next_all: *mut Chunk,
    /// The owner's list of chunks with a block to hand out.
    prev_partial: *mut Chunk,
    next_partial: *mut Chunk,
    in_partial: bool,
}

/// The shared part of chunk `c`.
///
/// # Safety
///
/// `c` is a live chunk.
unsafe fn shared<'a>(c: *mut Chunk) -> &'a ChunkShared {
    // SAFETY: the caller's contract; only this part is borrowed.
    unsafe { &(*c).shared }
}

/// The owner's part of chunk `c`.
///
/// # Safety
///
/// `c` is a live chunk of the calling thread's, and no other borrow of its
/// owner part is live.
unsafe fn own<'a>(c: *mut Chunk) -> &'a mut ChunkOwn {
    // SAFETY: the caller's contract; only this part is borrowed.
    unsafe { &mut *(*c).own.get() }
}

/// The chunks of each class alive now, for the tests (each test uses classes
/// no other test touches).
#[cfg(test)]
static LIVE_CHUNKS: [core::sync::atomic::AtomicIsize; CLASS_SIZES.len()] =
    [const { core::sync::atomic::AtomicIsize::new(0) }; CLASS_SIZES.len()];

/// The layout of a chunk.
fn chunk_layout() -> Layout {
    // SAFETY: CHUNK_BYTES is a power of two and non-zero.
    unsafe { Layout::from_size_align_unchecked(CHUNK_BYTES, CHUNK_BYTES) }
}

/// Frees a chunk's memory and its reference to the inbox.
///
/// # Safety
///
/// Nothing reaches the chunk or any of its blocks any more.
unsafe fn free_chunk(chunk: *mut Chunk) {
    // SAFETY: the caller's contract: the header is initialised and unreached.
    let inbox = unsafe { shared(chunk) }.inbox;
    #[cfg(test)]
    // SAFETY: as above.
    LIVE_CHUNKS[unsafe { shared(chunk) }.class].fetch_sub(1, Relaxed);
    // SAFETY: as above; the header's atomics may hold resources (shuttle's
    // vector clocks), so they are dropped before the memory goes.
    unsafe { ptr::drop_in_place(chunk) };
    // SAFETY: allocated by `new_chunk` with this layout.
    unsafe { dealloc(chunk.cast(), chunk_layout()) };
    // SAFETY: the chunk held a reference to its inbox.
    unsafe { release_inbox(inbox) };
}

/// The id of the next thread to make a chunk (0 means none).
static NEXT_OWNER: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(1);

/// A fresh owner id: never handed out before, so a chunk's id names one thread.
pub(crate) fn new_owner() -> usize {
    NEXT_OWNER.fetch_add(1, Relaxed)
}

/// One thread's chunks of one class.
pub(crate) struct SlabClass {
    inbox: *mut Inbox,
    all: *mut Chunk,
    partial: *mut Chunk,
    /// The one empty chunk kept (on the partial list), if any.
    spare: *mut Chunk,
}

impl SlabClass {
    pub(crate) const fn new() -> SlabClass {
        SlabClass {
            inbox: ptr::null_mut(),
            all: ptr::null_mut(),
            partial: ptr::null_mut(),
            spare: ptr::null_mut(),
        }
    }

    /// A block for owner `owner`: from a chunk with one to hand out, from the
    /// blocks other threads gave back, or from a new chunk.
    pub(crate) fn alloc(&mut self, class: usize, owner: usize) -> *mut u8 {
        loop {
            let c = self.partial;
            if c.is_null() {
                if !self.drain_inbox() {
                    self.new_chunk(class, owner);
                }
                continue;
            }
            if c == self.spare {
                self.spare = ptr::null_mut();
            }
            // SAFETY: a chunk of this thread's lists is live.
            debug_assert_eq!(unsafe { shared(c) }.class, class);
            // SAFETY: as above, and its owner part is this thread's.
            let chunk = unsafe { own(c) };
            if !chunk.local.is_null() {
                let block = chunk.local;
                // SAFETY: a free block of the chunk's list.
                chunk.local = unsafe { next_of(block) };
                chunk.used += 1;
                return block;
            }
            if chunk.carved < capacity(class) {
                let offset = HEADER_BYTES + chunk.carved * CLASS_SIZES[class];
                chunk.carved += 1;
                chunk.used += 1;
                // SAFETY: within the chunk: `carved < capacity`.
                return unsafe { c.cast::<u8>().add(offset) };
            }
            self.unlink_partial(c);
        }
    }

    /// Gives back a block of a chunk this thread owns.
    ///
    /// # Safety
    ///
    /// `block` came from [`alloc`](Self::alloc) of this slab, is free and
    /// reached by nothing else.
    pub(crate) unsafe fn release_own(&mut self, block: *mut u8) {
        let c = chunk_of(block);
        // SAFETY: the block's chunk is one of this thread's, kept alive by it.
        let chunk = unsafe { own(c) };
        // SAFETY: the caller's contract: a free block.
        unsafe { set_next(block, chunk.local) };
        chunk.local = block;
        chunk.used -= 1;
        self.settle(c);
    }

    /// A chunk got a block back: free it if that emptied it, unless it is
    /// kept as the class's one empty chunk; list it as having blocks to hand
    /// out otherwise.
    fn settle(&mut self, c: *mut Chunk) {
        // SAFETY: one of this thread's chunks.
        let (used, in_partial) = {
            let chunk = unsafe { own(c) };
            (chunk.used, chunk.in_partial)
        };
        if used == 0 && !self.spare.is_null() && self.spare != c {
            if in_partial {
                self.unlink_partial(c);
            }
            self.unlink_all(c);
            // SAFETY: no block of the chunk is out, and it is off the lists.
            unsafe { free_chunk(c) };
            return;
        }
        if used == 0 {
            self.spare = c;
        }
        if !in_partial {
            self.link_partial(c);
        }
    }

    /// Takes the blocks other threads gave back into their chunks' free
    /// lists. Answers whether there were any.
    fn drain_inbox(&mut self) -> bool {
        if self.inbox.is_null() {
            return false;
        }
        // SAFETY: this thread holds a reference to its inbox.
        let mut block = unsafe { &*self.inbox }.blocks.swap(0, Acquire) as *mut u8;
        let any = !block.is_null();
        while !block.is_null() {
            // SAFETY: a block pushed on the inbox, its first word the next one.
            let next = unsafe { next_of(block) };
            // SAFETY: a block of one of this thread's chunks, now free.
            unsafe { self.release_own(block) };
            block = next;
        }
        any
    }

    /// Makes a chunk of `class` and lists it first, to carve from.
    fn new_chunk(&mut self, class: usize, owner: usize) {
        if self.inbox.is_null() {
            self.inbox = Box::into_raw(Box::new(Inbox {
                blocks: AtomicUsize::new(0),
                refs: AtomicUsize::new(1),
            }));
        }
        // SAFETY: the layout's size is not zero.
        let c = unsafe { alloc(chunk_layout()) }.cast::<Chunk>();
        if c.is_null() {
            handle_alloc_error(chunk_layout());
        }
        // SAFETY: this thread holds a reference to its inbox.
        unsafe { &*self.inbox }.refs.fetch_add(1, Relaxed);
        #[cfg(test)]
        LIVE_CHUNKS[class].fetch_add(1, Relaxed);
        // SAFETY: a fresh allocation of the chunk's layout, its header first.
        unsafe {
            c.write(Chunk {
                shared: ChunkShared {
                    outstanding: AtomicUsize::new(0),
                    inbox: self.inbox,
                    owner,
                    class,
                },
                own: UnsafeCell::new(ChunkOwn {
                    carved: 0,
                    used: 0,
                    local: ptr::null_mut(),
                    prev_all: ptr::null_mut(),
                    next_all: self.all,
                    prev_partial: ptr::null_mut(),
                    next_partial: ptr::null_mut(),
                    in_partial: false,
                }),
            })
        };
        if !self.all.is_null() {
            // SAFETY: one of this thread's chunks.
            unsafe { own(self.all) }.prev_all = c;
        }
        self.all = c;
        self.link_partial(c);
    }

    fn link_partial(&mut self, c: *mut Chunk) {
        if !self.partial.is_null() {
            // SAFETY: one of this thread's chunks, not `c` (which is off the list).
            unsafe { own(self.partial) }.prev_partial = c;
        }
        // SAFETY: one of this thread's chunks.
        let chunk = unsafe { own(c) };
        chunk.prev_partial = ptr::null_mut();
        chunk.next_partial = self.partial;
        chunk.in_partial = true;
        self.partial = c;
    }

    fn unlink_partial(&mut self, c: *mut Chunk) {
        // SAFETY: one of this thread's chunks, on its partial list.
        let (prev, next) = {
            let chunk = unsafe { own(c) };
            chunk.in_partial = false;
            (chunk.prev_partial, chunk.next_partial)
        };
        if prev.is_null() {
            self.partial = next;
        } else {
            // SAFETY: its neighbours on the list are this thread's chunks too.
            unsafe { own(prev) }.next_partial = next;
        }
        if !next.is_null() {
            // SAFETY: as above.
            unsafe { own(next) }.prev_partial = prev;
        }
    }

    fn unlink_all(&mut self, c: *mut Chunk) {
        // SAFETY: one of this thread's chunks.
        let (prev, next) = {
            let chunk = unsafe { own(c) };
            (chunk.prev_all, chunk.next_all)
        };
        if prev.is_null() {
            self.all = next;
        } else {
            // SAFETY: its neighbours on the list are this thread's chunks too.
            unsafe { own(prev) }.next_all = next;
        }
        if !next.is_null() {
            // SAFETY: as above.
            unsafe { own(next) }.prev_all = prev;
        }
    }

    /// The owner exits: every chunk with no block out is freed; every other
    /// one gets the count of its blocks out, and the inbox is closed, so the
    /// last thread to give a block back frees the chunk.
    pub(crate) fn orphan(&mut self) {
        if self.inbox.is_null() {
            return;
        }
        self.drain_inbox();
        let mut c = self.all;
        while !c.is_null() {
            // SAFETY: one of this thread's chunks.
            let (next, used) = {
                let chunk = unsafe { own(c) };
                (chunk.next_all, chunk.used)
            };
            if used == 0 {
                // SAFETY: no block of it is out, and the lists go away below.
                unsafe { free_chunk(c) };
            } else {
                // SAFETY: as above.
                unsafe { shared(c) }.outstanding.store(used, Relaxed);
            }
            c = next;
        }
        self.all = ptr::null_mut();
        self.partial = ptr::null_mut();
        self.spare = ptr::null_mut();
        // SAFETY: this thread holds a reference to its inbox. Release: a
        // thread that finds it closed sees every count written above.
        let mut block = unsafe { &*self.inbox }.blocks.swap(CLOSED, AcqRel) as *mut u8;
        while !block.is_null() {
            // SAFETY: a block pushed on the inbox before it closed.
            let next = unsafe { next_of(block) };
            // SAFETY: its chunk is orphaned now; this counts the block back.
            unsafe { count_down(chunk_of(block)) };
            block = next;
        }
        // SAFETY: the owner's reference, given up.
        unsafe { release_inbox(self.inbox) };
        self.inbox = ptr::null_mut();
    }
}

/// Counts a block of an orphaned chunk back, freeing the chunk with its last.
///
/// # Safety
///
/// The chunk is orphaned and the caller gives back one of its blocks out.
unsafe fn count_down(chunk: *mut Chunk) {
    // SAFETY: the block the caller holds keeps the chunk alive until here.
    if unsafe { shared(chunk) }.outstanding.fetch_sub(1, AcqRel) == 1 {
        // SAFETY: every block is back: nothing reaches the chunk.
        unsafe { free_chunk(chunk) };
    }
}

/// Gives back a block of the slab layer from a thread that does not own its
/// chunk (or whose cache is gone): onto the owner's inbox, or, once the owner
/// exited, counted down.
///
/// # Safety
///
/// `block` came from the slab layer, is free and reached by nothing else.
pub(crate) unsafe fn release_remote(block: *mut u8) {
    let c = chunk_of(block);
    // SAFETY: the block keeps its chunk, and the inbox the chunk names, alive.
    let inbox = unsafe { &*shared(c).inbox };
    // Acquire, as the failed compare-and-swap below: a closed inbox's
    // counts, written before the owner's swap, are seen by the count-down.
    let mut head = inbox.blocks.load(Acquire);
    loop {
        if head & CLOSED != 0 {
            // SAFETY: the owner exited after writing the chunk's count.
            unsafe { count_down(c) };
            return;
        }
        // SAFETY: a free block: its first word is ours to write.
        unsafe { set_next(block, head as *mut u8) };
        // Release: the owner, draining with an acquire swap, reads the link.
        match inbox
            .blocks
            .compare_exchange_weak(head, block as usize, Release, Acquire)
        {
            Ok(_) => return,
            Err(now) => head = now,
        }
    }
}

/// Gives back a block of the slab layer from any thread: to the owner's free
/// list when `slab` is that owner's, otherwise remotely.
///
/// # Safety
///
/// As for [`release_remote`].
pub(crate) unsafe fn release(block: *mut u8, mine: Option<(&mut SlabClass, usize)>) {
    match mine {
        // SAFETY: the block's chunk is live; its owner id is fixed.
        Some((slab, owner)) if unsafe { shared(chunk_of(block)) }.owner == owner => {
            // SAFETY: the caller's contract; the chunk is this thread's.
            unsafe { slab.release_own(block) }
        }
        // SAFETY: the caller's contract.
        _ => unsafe { release_remote(block) },
    }
}

/// A block for a thread whose cache is gone (it is exiting): a chunk of its
/// own, orphaned from the start, freed when the block comes back.
pub(crate) fn lone_block(class: usize) -> *mut u8 {
    let mut slab = SlabClass::new();
    let block = slab.alloc(class, 0);
    slab.orphan();
    block
}

#[cfg(test)]
mod tests;
