#![doc(
    html_logo_url = "https://raw.githubusercontent.com/vertexclique/kovan/master/art/kovan-square.svg"
)]
//! # Kovan MVCC
//!
//! `kovan-mvcc` is a Multi-Version Concurrency Control (MVCC) implementation based on the Percolator model,
//! built on top of the `kovan` memory reclamation system.
//!
//! It provides snapshot isolation (`begin_with_isolation(IsolationLevel::RepeatableRead)`), serializable
//! snapshot isolation (`IsolationLevel::Serializable`) and read committed (`begin()`, the default), and supports
//! distributed transactions (conceptually, though currently local).
//!
//! ## How it works
//!
//! The system uses a `LockTable` to manage active transactions and a `Storage` layer to persist versioned data.
//!
//! - **Writes**: Buffered locally and applied atomically at commit time using a 2-Phase Commit (2PC) protocol (Prewrite, Commit).
//! - **Reads**: performed at a specific timestamp (snapshot), ignoring data committed after the start timestamp. A
//!   read that meets another transaction's lock waits as the backoff strategy says, and answers
//!   `Err(MvccError::LockConflict)` when it gives up.
//! - **GC**: `Storage::gc_writes` and `Storage::gc_data` collect versions below `KovanMVCC::gc_watermark()`.
//!
//! ## Example
//!
//! ```rust
//! use kovan_mvcc::KovanMVCC;
//!
//! let db = KovanMVCC::new();
//!
//! // 1. Write a value
//! let mut txn = db.begin();
//! txn.write("key1", b"value1".to_vec()).unwrap();
//! txn.commit().unwrap();
//!
//! // 2. Read the value
//! let txn = db.begin();
//! let val = txn.read("key1").unwrap().expect("Should find key");
//! assert_eq!(val, b"value1");
//! ```

pub mod backoff;
pub mod error;
mod lock_table;
pub mod percolator;
pub mod storage;
mod timestamp_oracle;

// Export KovanMVCC and Txn directly from percolator
pub use crate::backoff::{BackoffAction, BackoffStrategy, DefaultBackoff};
pub use crate::error::MvccError;
pub use crate::lock_table::{LockInfo, LockTable, LockType};
pub use crate::percolator::{
    ActiveTxnRegistry, InflightWriteRegistry, IsolationLevel, KovanMVCC, Txn,
};
pub use crate::storage::{InMemoryStorage, Storage, Value, WriteInfo, WriteKind};
pub use crate::timestamp_oracle::{LocalTimestampOracle, MockTimestampOracle, TimestampOracle};
