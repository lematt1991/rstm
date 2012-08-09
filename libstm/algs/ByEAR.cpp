/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

/**
 *  ByEAR Implementation
 *
 *    This code is like ByteEager, except we have redo logs, and we also use an
 *    aggressive contention manager (abort other on conflict).
 */

#include "../profiling.hpp"
#include "../algs.hpp"
#include "../RedoRAWUtils.hpp"

using stm::UNRECOVERABLE;
using stm::TxThread;
using stm::ByteLockList;
using stm::bytelock_t;
using stm::get_bytelock;
using stm::WriteSetEntry;
using stm::threads;


/**
 *  Declare the functions that we're going to implement, so that we can avoid
 *  circular dependencies.
 */
namespace {
  struct ByEAR
  {
      static void begin(TX_LONE_PARAMETER);
      static TM_FASTCALL void* read_ro(TX_FIRST_PARAMETER STM_READ_SIG(,));
      static TM_FASTCALL void* read_rw(TX_FIRST_PARAMETER STM_READ_SIG(,));
      static TM_FASTCALL void write_ro(TX_FIRST_PARAMETER STM_WRITE_SIG(,,));
      static TM_FASTCALL void write_rw(TX_FIRST_PARAMETER STM_WRITE_SIG(,,));
      static TM_FASTCALL void commit_ro(TX_LONE_PARAMETER);
      static TM_FASTCALL void commit_rw(TX_LONE_PARAMETER);

      static void rollback(STM_ROLLBACK_SIG(,,));
      static bool irrevoc(TxThread*);
      static void onSwitchTo();
  };

  /**
   *  Define the states for a transaction
   */
#define TX_ACTIVE     0u
#define TX_ABORTED    1u
#define TX_COMMITTED  2u

  /**
   *  ByEAR begin:
   */
  void ByEAR::begin(TX_LONE_PARAMETER)
  {
      TX_GET_TX_INTERNAL;
      tx->allocator.onTxBegin();
      // set self to active
      tx->alive = TX_ACTIVE;
  }

  /**
   *  ByEAR commit (read-only):
   */
  void
  ByEAR::commit_ro(TX_LONE_PARAMETER)
  {
      TX_GET_TX_INTERNAL;
      // read-only... release read locks
      foreach (ByteLockList, i, tx->r_bytelocks)
          (*i)->reader[tx->id-1] = 0;

      tx->r_bytelocks.reset();
      OnReadOnlyCommit(tx);
  }

  /**
   *  ByEAR commit (writing context):
   */
  void
  ByEAR::commit_rw(TX_LONE_PARAMETER)
  {
      TX_GET_TX_INTERNAL;
      // atomically mark self committed
      if (!bcas32(&tx->alive, TX_ACTIVE, TX_COMMITTED))
          stm::tmabort();

      // we committed... replay redo log
      tx->writes.writeback();
      CFENCE;

      // release write locks, then read locks
      foreach (ByteLockList, i, tx->w_bytelocks)
          (*i)->owner = 0;
      foreach (ByteLockList, i, tx->r_bytelocks)
          (*i)->reader[tx->id-1] = 0;

      // clean-up
      tx->r_bytelocks.reset();
      tx->w_bytelocks.reset();
      tx->writes.reset();
      OnReadWriteCommit(tx, read_ro, write_ro, commit_ro);
  }

  /**
   *  ByEAR read (read-only transaction)
   */
  void*
  ByEAR::read_ro(TX_FIRST_PARAMETER STM_READ_SIG(addr,))
  {
      TX_GET_TX_INTERNAL;
      bytelock_t* lock = get_bytelock(addr);

      // do I have a read lock?
      if (lock->reader[tx->id-1] == 0) {
          // first time read, log this location
          tx->r_bytelocks.insert(lock);
          // mark my lock byte
          lock->set_read_byte(tx->id-1);
      }

      if (uint32_t owner = lock->owner) {
          switch (threads[owner-1]->alive) {
            case TX_COMMITTED:
              // abort myself if the owner is writing back
              stm::tmabort();
            case TX_ACTIVE:
              // abort the owner(it's active)
              if (!bcas32(&threads[owner-1]->alive, TX_ACTIVE, TX_ABORTED))
                  stm::tmabort();
              break;
            case TX_ABORTED:
              // if the owner is unwinding, go through and read
              break;
          }
      }

      // do the read
      CFENCE;
      void* result = *addr;
      CFENCE;

      // check for remote abort
      if (tx->alive == TX_ABORTED)
          stm::tmabort();
      return result;
  }

  /**
   *  ByEAR read (writing transaction)
   */
  void*
  ByEAR::read_rw(TX_FIRST_PARAMETER STM_READ_SIG(addr,mask))
  {
      TX_GET_TX_INTERNAL;
      bytelock_t* lock = get_bytelock(addr);

      // skip instrumentation if I am the writer
      if (lock->owner == tx->id) {
          // [lyj] a liveness check can be inserted but not necessary
          // check the log
          WriteSetEntry log(STM_WRITE_SET_ENTRY(addr, NULL, mask));
          bool found = tx->writes.find(log);
          REDO_RAW_CHECK(found, log, mask);

          void* val = *addr;
          REDO_RAW_CLEANUP(val, found, log, mask);
          return val;
      }

      // do I have a read lock?
      if (lock->reader[tx->id-1] == 0) {
          // first time read, log this location
          tx->r_bytelocks.insert(lock);
          // mark my lock byte
          lock->set_read_byte(tx->id-1);
      }

      if (uint32_t owner = lock->owner) {
          switch (threads[owner-1]->alive) {
            case TX_COMMITTED:
              // abort myself if the owner is writing back
              stm::tmabort();
            case TX_ACTIVE:
              // abort the owner(it's active)
              if (!bcas32(&threads[owner-1]->alive, TX_ACTIVE, TX_ABORTED))
                  stm::tmabort();
              break;
            case TX_ABORTED:
              // if the owner is unwinding, go through and read
              break;
          }
      }

      // do the read
      CFENCE;
      void* result = *addr;
      CFENCE;

      // check for remote abort
      if (tx->alive == TX_ABORTED)
          stm::tmabort();

      return result;
  }

  /**
   *  ByEAR write (read-only context)
   */
  void
  ByEAR::write_ro(TX_FIRST_PARAMETER STM_WRITE_SIG(addr,val,mask))
  {
      TX_GET_TX_INTERNAL;
      bytelock_t* lock = get_bytelock(addr);

      // abort current owner, wait for release, then acquire
      while (true) {
          // abort the owner if there is one
          if (uint32_t owner = lock->owner)
              cas32(&threads[owner-1]->alive, TX_ACTIVE, TX_ABORTED);
          // try to get ownership
          else if (bcas32(&(lock->owner), 0u, tx->id))
              break;
          // liveness check
          if (tx->alive == TX_ABORTED)
              stm::tmabort();
      }

      // log the lock, drop any read locks I have
      tx->w_bytelocks.insert(lock);
      lock->reader[tx->id-1] = 0;

      // abort active readers
      //
      // [lyj] here we must use the cas to abort the reader, otherwise we would
      //       risk setting the state of a committing transaction to aborted,
      //       which can give readers inconsistent results when they trying to
      //       read while the committer is writing back.
      for (int i = 0; i < 60; ++i)
          if (lock->reader[i] != 0 && threads[i]->alive == TX_ACTIVE)
              if (!bcas32(&threads[i]->alive, TX_ACTIVE, TX_ABORTED))
                  stm::tmabort();

      // add to redo log
      tx->writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));

      stm::OnFirstWrite(tx, read_rw, write_rw, commit_rw);
  }

  /**
   *  ByEAR write (writing context)
   */
  void
  ByEAR::write_rw(TX_FIRST_PARAMETER STM_WRITE_SIG(addr,val,mask))
  {
      TX_GET_TX_INTERNAL;
      bytelock_t* lock = get_bytelock(addr);

      // fastpath for repeat writes to the same location
      if (lock->owner == tx->id) {
          tx->writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
          return;
      }

      // abort current owner, wait for release, then acquire
      while (true) {
          // abort the owner if there is one
          if (uint32_t owner = lock->owner)
              cas32(&threads[owner-1]->alive, TX_ACTIVE, TX_ABORTED);
          // try to get ownership
          else if (bcas32(&(lock->owner), 0u, tx->id))
              break;
          // liveness check
          if (tx->alive == TX_ABORTED)
              stm::tmabort();
      }

      // log the lock, drop any read locks I have
      tx->w_bytelocks.insert(lock);
      lock->reader[tx->id-1] = 0;

      // abort active readers
      for (int i = 0; i < 60; ++i)
          if (lock->reader[i] != 0 && threads[i]->alive == TX_ACTIVE)
              if (!bcas32(&threads[i]->alive, TX_ACTIVE, TX_ABORTED))
                  stm::tmabort();

      // add to redo log
      tx->writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
  }

  /**
   *  ByEAR unwinder:
   */
  void
  ByEAR::rollback(STM_ROLLBACK_SIG(tx, except, len))
  {
      PreRollback(tx);

      // Perform writes to the exception object if there were any... taking the
      // branch overhead without concern because we're not worried about
      // rollback overheads.
      STM_ROLLBACK(tx->writes, except, len);

      // release write locks, then read locks
      foreach (ByteLockList, i, tx->w_bytelocks)
          (*i)->owner = 0;
      foreach (ByteLockList, i, tx->r_bytelocks)
          (*i)->reader[tx->id-1] = 0;

      // reset lists
      tx->r_bytelocks.reset();
      tx->w_bytelocks.reset();
      tx->writes.reset();

      // randomized exponential backoff
      exp_backoff(tx);

      PostRollback(tx, read_ro, write_ro, commit_ro);
  }

  /**
   *  ByEAR in-flight irrevocability:
   */
  bool
  ByEAR::irrevoc(TxThread*)
  {
      return false;
  }

  /**
   *  Switch to ByEAR:
   */
  void ByEAR::onSwitchTo() { }
}

namespace stm {
  /**
   *  ByEAR initialization
   */
  template<>
  void initTM<ByEAR>()
  {
      // set the name
      stms[ByEAR].name      = "ByEAR";

      // set the pointers
      stms[ByEAR].begin     = ::ByEAR::begin;
      stms[ByEAR].commit    = ::ByEAR::commit_ro;
      stms[ByEAR].read      = ::ByEAR::read_ro;
      stms[ByEAR].write     = ::ByEAR::write_ro;
      stms[ByEAR].rollback  = ::ByEAR::rollback;
      stms[ByEAR].irrevoc   = ::ByEAR::irrevoc;
      stms[ByEAR].switcher  = ::ByEAR::onSwitchTo;
      stms[ByEAR].privatization_safe = true;
  }
}

#ifdef STM_ONESHOT_ALG_ByEAR
DECLARE_AS_ONESHOT_NORMAL(ByEAR)
#endif
