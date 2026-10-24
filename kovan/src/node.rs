//! Allocating, freeing and retiring the nodes of kovan structures.
//!
//! A structure that publishes nodes through [`Atomic`](crate::Atomic)
//! allocates each one with [`alloc_node`] (or holds it as a [`NodeBox`] until
//! it is published) and lets it go with exactly one of
//! [`retire_node`] (it was published: free it once no guard can reach it),
//! [`drop_node`] (no other thread can reach it: drop its value and free it
//! now) or [`free_node`] (its value was moved out or never written: free the
//! memory only). [`alloc_node_uninit`] gives the memory of a node whose fields
//! are written in place.
//!
//! Without the `recycle` feature these are `Box` allocations and frees, and
//! [`retire_node`] is [`retire`](crate::retire). With it, a node of up to
//! 1 KiB aligned to at most 16 bytes takes its memory from, and gives it back
//! to, a per-thread magazine cache of its size class (see the `recycle`
//! feature in the crate documentation), so the steady state of a structure
//! that publishes and retires nodes makes no call into the global allocator.
//! Either way the four functions pair with one another only: a node from
//! [`alloc_node`] must not be freed as a `Box`, and a `Box` must not be freed
//! with [`drop_node`].
//!
//! A node's value is written whole on allocation, its
//! [`RetiredNode`](crate::RetiredNode) header included, so a node whose
//! memory a cache hands back is a fresh node in every respect, as the
//! recycling contract of [`Reclaimable`](crate::Reclaimable) requires.

use alloc::boxed::Box;
use core::fmt;
use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;

#[cfg(feature = "recycle")]
use crate::recycle::{NO_CLASS, alloc_block, class_of, free_block};
#[cfg(feature = "recycle")]
use crate::retired::RetiredNode;

/// The magazine class of `T`, worked out once per type at compile time.
#[cfg(feature = "recycle")]
struct Class<T>(core::marker::PhantomData<T>);

#[cfg(feature = "recycle")]
impl<T> Class<T> {
    const INDEX: usize = class_of(core::mem::size_of::<T>(), core::mem::align_of::<T>());
}

/// Allocates a node holding `value` and returns a pointer to it, for
/// [`Atomic::new`](crate::Atomic::new) or a store or compare-and-swap of an
/// [`Atomic`](crate::Atomic).
///
/// The node is let go with [`retire_node`], [`drop_node`] or [`free_node`].
///
/// ```
/// use kovan::{Atomic, RetiredNode, Shared, alloc_node, drop_node, pin, retire_node};
/// use std::sync::atomic::Ordering;
///
/// #[repr(C)]
/// struct Node {
///     retired: RetiredNode,
///     value: u64,
/// }
///
/// let slot = Atomic::new(alloc_node(Node { retired: RetiredNode::new(), value: 1 }));
/// let guard = pin();
/// let next = alloc_node(Node { retired: RetiredNode::new(), value: 2 });
/// // SAFETY: a fresh node, published here once.
/// let old = slot.swap(unsafe { Shared::from_raw(next) }, Ordering::AcqRel, &guard);
/// // SAFETY: the swap unlinked `old`; it is retired once.
/// unsafe { retire_node(old.as_raw()) };
/// // SAFETY: the guard keeps the current node; read it, then let it go with the slot.
/// assert_eq!(unsafe { slot.load(Ordering::Acquire, &guard).deref() }.value, 2);
/// drop(guard);
/// // SAFETY: no other thread can reach the slot's node any more.
/// unsafe { drop_node(slot.load(Ordering::Acquire, &pin()).as_raw()) };
/// ```
#[inline]
pub fn alloc_node<T>(value: T) -> *mut T {
    let node = alloc_node_uninit::<T>().cast::<T>();
    // SAFETY: a fresh allocation for a `T`, which nothing else reaches yet.
    unsafe { node.write(value) };
    node
}

/// Allocates the memory of a node of `T`, its value not yet written, for a
/// node whose fields are written in place.
///
/// The node is let go with [`free_node`] while its value is not (or no
/// longer) written, and with [`retire_node`] or [`drop_node`] once it is.
#[inline]
pub fn alloc_node_uninit<T>() -> *mut MaybeUninit<T> {
    #[cfg(feature = "recycle")]
    if Class::<T>::INDEX != NO_CLASS {
        return alloc_block(Class::<T>::INDEX).cast();
    }
    Box::into_raw(Box::<T>::new_uninit())
}

/// Drops the value of a node from [`alloc_node`] and frees the node now.
///
/// # Safety
///
/// `node` came from [`alloc_node`] (or [`alloc_node_uninit`], with its value
/// written since) for this `T`, no other thread can reach it, and it is let go
/// only this once.
#[inline]
pub unsafe fn drop_node<T>(node: *mut T) {
    // SAFETY: the caller's contract: the value is initialised and nobody else
    // reaches it.
    unsafe { core::ptr::drop_in_place(node) };
    // SAFETY: the value was just dropped; the memory is the caller's to free.
    unsafe { free_node(node) };
}

/// Frees the memory of a node from [`alloc_node`] or [`alloc_node_uninit`]
/// without dropping a value: one that was never written, or was moved out.
///
/// # Safety
///
/// `node` came from [`alloc_node`] or [`alloc_node_uninit`] for this `T`, it
/// holds no value that still needs dropping, no other thread can reach it, and
/// it is let go only this once.
#[inline]
pub unsafe fn free_node<T>(node: *mut T) {
    #[cfg(feature = "recycle")]
    if Class::<T>::INDEX != NO_CLASS {
        // SAFETY: the caller's contract; a node of this class came from
        // `alloc_block` of the same class.
        unsafe { free_block(node.cast(), Class::<T>::INDEX) };
        return;
    }
    // `MaybeUninit` has no drop glue: this frees the memory only.
    // SAFETY: the caller's contract; a node outside every class is a `Box`.
    drop(unsafe { Box::from_raw(node.cast::<MaybeUninit<T>>()) });
}

/// Retires a node from [`alloc_node`] that was unlinked from every
/// [`Atomic`](crate::Atomic): once no guard can reach it, its value is
/// dropped and its memory freed (to the magazine cache under the `recycle`
/// feature), as [`retire`](crate::retire) does for a `Box`.
///
/// # Safety
///
/// As for [`retire`](crate::retire): `node` came from [`alloc_node`] for this
/// `T`, a `#[repr(C)]` type whose first field is a
/// [`RetiredNode`](crate::RetiredNode); it is unlinked; it is retired once and
/// not used afterwards except through pointers that guards loaded while it
/// was reachable (see [`Atomic::load`](crate::Atomic::load)).
#[inline]
pub unsafe fn retire_node<T: 'static>(node: *mut T) {
    #[cfg(feature = "recycle")]
    if Class::<T>::INDEX != NO_CLASS {
        // SAFETY: the caller's contract; `drop_retired` drops the value and
        // gives the memory back to the class it came from.
        unsafe { crate::guard::retire_with(node.cast::<RetiredNode>(), drop_retired::<T>) };
        return;
    }
    // SAFETY: the caller's contract; a node outside every class is a `Box`.
    unsafe { crate::retire(node) }
}

/// The destructor [`retire_node`] gives a node of a magazine class.
///
/// # Safety
///
/// `node` is a node of `T` from [`alloc_node`] that no guard can reach.
#[cfg(feature = "recycle")]
unsafe fn drop_retired<T>(node: *mut RetiredNode) {
    // SAFETY: the reclamation walk calls this once, when nothing reaches the
    // node, and reads nothing of it afterwards.
    unsafe { drop_node(node.cast::<T>()) }
}

/// An owned node from [`alloc_node`] that is not published yet: it drops its
/// value and frees itself when dropped, like a `Box`, through the node
/// helpers (so under the `recycle` feature its memory goes back to the
/// magazine cache).
///
/// A structure keeps an unpublished node in a `NodeBox` (across the attempts
/// of a compare-and-swap, say), publishes it with [`into_raw`](Self::into_raw)
/// and takes back one whose publication failed with
/// [`from_raw`](Self::from_raw), exactly as it would a `Box`.
///
/// ```
/// use kovan::{NodeBox, RetiredNode};
///
/// #[repr(C)]
/// struct Node {
///     retired: RetiredNode,
///     value: u64,
/// }
///
/// let mut node = NodeBox::new(Node { retired: RetiredNode::new(), value: 1 });
/// node.value += 1;
/// let raw = NodeBox::into_raw(node);
/// // SAFETY: `raw` came from `into_raw` and nothing else owns it.
/// let node = unsafe { NodeBox::from_raw(raw) };
/// assert_eq!(node.value, 2);
/// ```
pub struct NodeBox<T> {
    node: NonNull<T>,
    _owns: PhantomData<T>,
}

impl<T> NodeBox<T> {
    /// Allocates a node holding `value`.
    #[inline]
    pub fn new(value: T) -> Self {
        // SAFETY: `alloc_node` never returns null.
        let node = unsafe { NonNull::new_unchecked(alloc_node(value)) };
        NodeBox {
            node,
            _owns: PhantomData,
        }
    }

    /// The node, for publication: the caller now owns it and lets it go with
    /// [`retire_node`], [`drop_node`], [`free_node`] or
    /// [`from_raw`](Self::from_raw).
    #[inline]
    pub fn into_raw(this: Self) -> *mut T {
        let node = this.node.as_ptr();
        mem::forget(this);
        node
    }

    /// Takes ownership of a node from [`alloc_node`] (or
    /// [`into_raw`](Self::into_raw)) back.
    ///
    /// # Safety
    ///
    /// `node` came from [`alloc_node`] or [`into_raw`](Self::into_raw) for
    /// this `T`, holds a value, is reached by no other thread, and is let go
    /// only through the returned `NodeBox`.
    #[inline]
    pub unsafe fn from_raw(node: *mut T) -> Self {
        // SAFETY: the caller's contract: a node pointer is never null.
        let node = unsafe { NonNull::new_unchecked(node) };
        NodeBox {
            node,
            _owns: PhantomData,
        }
    }
}

impl<T> Deref for NodeBox<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: the node is owned and initialised.
        unsafe { self.node.as_ref() }
    }
}

impl<T> DerefMut for NodeBox<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: the node is owned and initialised.
        unsafe { self.node.as_mut() }
    }
}

impl<T> Drop for NodeBox<T> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: the node is owned, initialised and reached by nobody else.
        unsafe { drop_node(self.node.as_ptr()) }
    }
}

impl<T: fmt::Debug> fmt::Debug for NodeBox<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

// SAFETY: a `NodeBox` owns its value as a `Box` does.
unsafe impl<T: Send> Send for NodeBox<T> {}
// SAFETY: as above.
unsafe impl<T: Sync> Sync for NodeBox<T> {}
