/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

// tick instead of timestamp, no timestamp scaling, and wang-style
// timestamps... this should be pretty good

/**
 *  OrecELA_amd64 Implementation:
 *
 *    This STM is similar to OrecELA, with three exceptions.  First, we use
 *    the x86 tick counter in place of a shared memory counter, which lets us
 *    avoid a bottleneck when committing small writers.  Second, we solve the
 *    "doomed transaction" half of the privatization problem by using a
 *    validation fence, instead of by using polling on the counter.  Third,
 *    we use that same validation fence to address delayed cleanup, instead
 *    of using an ticket counter.
 */

#include "../profiling.hpp"
#include "../cm.hpp"
#include "../algs.hpp"
#include "../RedoRAWUtils.hpp"

using stm::TxThread;
using stm::get_orec;
using stm::WriteSetEntry;
using stm::OrecList;
using stm::WriteSet;
using stm::orec_t;
using stm::id_version_t;

namespace
{
  template <class CM>
  struct OrecELA_amd64_Generic
  {
      static TM_FASTCALL bool begin();
      static TM_FASTCALL void* read_ro(STM_READ_SIG(,));
      static TM_FASTCALL void* read_rw(STM_READ_SIG(,));
      static TM_FASTCALL void write_ro(STM_WRITE_SIG(,,));
      static TM_FASTCALL void write_rw(STM_WRITE_SIG(,,));
      static TM_FASTCALL void commit_ro();
      static TM_FASTCALL void commit_rw();

      static void rollback(STM_ROLLBACK_SIG(,,));
      static void Initialize(int id, const char* name);
  };

  void onSwitchTo();
  bool irrevoc(TxThread*);
  NOINLINE void validate(TxThread*);

  template <class CM>
  void
  OrecELA_amd64_Generic<CM>::Initialize(int id, const char* name)
  {
      // set the name
      stm::stms[id].name      = name;

      // set the pointers
      stm::stms[id].begin     = OrecELA_amd64_Generic<CM>::begin;
      stm::stms[id].commit    = OrecELA_amd64_Generic<CM>::commit_ro;
      stm::stms[id].read      = OrecELA_amd64_Generic<CM>::read_ro;
      stm::stms[id].write     = OrecELA_amd64_Generic<CM>::write_ro;
      stm::stms[id].rollback  = OrecELA_amd64_Generic<CM>::rollback;
      stm::stms[id].irrevoc   = irrevoc;
      stm::stms[id].switcher  = onSwitchTo;
      stm::stms[id].privatization_safe = true;
  }

  /**
   *  OrecELA_amd64 begin:
   *
   *    Sample the timestamp and prepare local vars
   */
  template <class CM>
  bool
  OrecELA_amd64_Generic<CM>::begin()
  {
      TxThread* tx = stm::Self;
      tx->allocator.onTxBegin();
      tx->start_time = tickp() & 0x7FFFFFFFFFFFFFFFLL;
      CM::onBegin(tx);
      return false;
  }

  /**
   *  OrecELA_amd64 commit (read-only context)
   *
   *    We just reset local fields and we're done
   */
  template <class CM>
  void
  OrecELA_amd64_Generic<CM>::commit_ro()
  {
      TxThread* tx = stm::Self;
      // notify CM
      CM::onCommit(tx);
      // read-only
      tx->r_orecs.reset();
      OnReadOnlyCommit(tx);
      tx->start_time = 0x7FFFFFFFFFFFFFFFLL;
  }

  /**
   *  OrecELA_amd64 commit (writing context)
   *
   *    Using Wang-style timestamps, we grab all locks, validate, writeback,
   *    increment the timestamp, and then release all locks.
   */
  template <class CM>
  void
  OrecELA_amd64_Generic<CM>::commit_rw()
  {
      TxThread* tx = stm::Self;
      // acquire locks
      foreach (WriteSet, i, tx->writes) {
          // get orec, read its version#
          orec_t* o = get_orec(i->addr);
          uintptr_t ivt = o->v.all;

          // lock all orecs, unless already locked
          if (ivt <= tx->start_time) {
              // abort if cannot acquire
              if (!bcasptr(&o->v.all, ivt, tx->my_lock.all))
                  tx->tmabort();
              // save old version to o->p, remember that we hold the lock
              o->p = ivt;
              tx->locks.insert(o);
          }
          // else if we don't hold the lock abort
          else if (ivt != tx->my_lock.all) {
              tx->tmabort();
          }
      }

      // validate
      foreach (OrecList, i, tx->r_orecs) {
          uintptr_t ivt = (*i)->v.all;
          // if unlocked and newer than start time, abort
          if ((ivt > tx->start_time) && (ivt != tx->my_lock.all))
              tx->tmabort();
      }

      // run the redo log
      tx->writes.writeback();

      // increment the global timestamp, release locks
      WBR; // for extremely small transactions, we're getting errors wrt the
           // timing of this tick... a WBR seems to resolve, though I don't
           // know why... tickp should be precise enough...
      CFENCE;
      uintptr_t end_time = tickp() & 0x7FFFFFFFFFFFFFFFLL;
      CFENCE;

      // announce that I'm done
      tx->start_time = 0x7FFFFFFFFFFFFFFFLL;

      // release locks
      foreach (OrecList, i, tx->locks)
          (*i)->v.all = end_time;

      // notify CM
      CM::onCommit(tx);

      // clean-up
      tx->r_orecs.reset();
      tx->writes.reset();
      tx->locks.reset();
      OnReadWriteCommit(tx, read_ro, write_ro, commit_ro);

      // quiesce
      CFENCE;
      for (int id = 0; id < stm::threadcount.val; ++id)
          while (stm::threads[id]->last_val_time < end_time) spin64();
  }

  /**
   *  OrecELA_amd64 read (read-only context):
   *
   *    in the best case, we just read the value, check the timestamp, log the
   *    orec and return
   */
  template <class CM>
  void* OrecELA_amd64_Generic<CM>::read_ro(STM_READ_SIG(addr,))
  {
      TxThread* tx = stm::Self;
      // get the orec addr
      orec_t* o = get_orec(addr);

      while (true) {
          // read the location
          void* tmp = *addr;
          CFENCE;
          //  check the orec.
          //  NB: with this variant of timestamp, we don't need prevalidation
          id_version_t ivt;
          ivt.all = o->v.all;

          // common case: new read to uncontended location
          if (ivt.all <= tx->start_time) {
              tx->r_orecs.insert(o);
              return tmp;
          }

          // if lock held, spin and retry
          if (ivt.fields.lock) {
              spin64();
              continue;
          }

          // scale timestamp if ivt is too new, then try again
          CFENCE;
          uint64_t newts = tickp() & 0x7FFFFFFFFFFFFFFFLL;
          CFENCE;
          validate(tx);
          tx->start_time = newts;
      }
  }

  /**
   *  OrecELA_amd64 read (writing context):
   *
   *    Just like read-only context, but must check the write set first
   */
  template <class CM>
  void*
  OrecELA_amd64_Generic<CM>::read_rw(STM_READ_SIG(addr,mask))
  {
      TxThread* tx = stm::Self;
      // check the log for a RAW hazard, we expect to miss
      WriteSetEntry log(STM_WRITE_SET_ENTRY(addr, NULL, mask));
      bool found = tx->writes.find(log);
      REDO_RAW_CHECK(found, log, mask);

      // reuse the ReadRO barrier, which is adequate here---reduces LOC
      void* val = read_ro(addr STM_MASK(mask));
      REDO_RAW_CLEANUP(val, found, log, mask);
      return val;
  }

  /**
   *  OrecELA_amd64 write (read-only context):
   *
   *    Buffer the write, and switch to a writing context
   */
  template <class CM>
  void
  OrecELA_amd64_Generic<CM>::write_ro(STM_WRITE_SIG(addr,val,mask))
  {
      TxThread* tx = stm::Self;
      // add to redo log
      tx->writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
      OnFirstWrite(tx, read_rw, write_rw, commit_rw);
  }

  /**
   *  OrecELA_amd64 write (writing context):
   *
   *    Just buffer the write
   */
  template <class CM>
  void
  OrecELA_amd64_Generic<CM>::write_rw(STM_WRITE_SIG(addr,val,mask))
  {
      TxThread* tx = stm::Self;
      // add to redo log
      tx->writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
  }

  /**
   *  OrecELA_amd64 rollback:
   *
   *    Release any locks we acquired (if we aborted during a commit()
   *    operation), and then reset local lists.
   */
  template <class CM>
  void
  OrecELA_amd64_Generic<CM>::rollback(STM_ROLLBACK_SIG(tx, except, len))
  {
      tx->last_val_time = 0x7FFFFFFFFFFFFFFFLL;
      PreRollback(tx);

      // Perform writes to the exception object if there were any... taking the
      // branch overhead without concern because we're not worried about
      // rollback overheads.
      STM_ROLLBACK(tx->writes, except, len);

      // release the locks and restore version numbers
      foreach (OrecList, i, tx->locks)
          (*i)->v.all = (*i)->p;

      // notify CM
      CM::onAbort(tx);

      // undo memory operations, reset lists
      tx->r_orecs.reset();
      tx->writes.reset();
      tx->locks.reset();
      PostRollback(tx, read_ro, write_ro, commit_ro);
  }

  /**
   *  OrecELA_amd64 in-flight irrevocability:
   *
   *    Either commit the transaction or return false.
   */
   bool irrevoc(TxThread* tx)
   {
       return false;
       // NB: In a prior release, we actually had a full OrecELA_amd64 commit
       //     here.  Any contributor who is interested in improving this code
       //     should note that such an approach is overkill: by the time this
       //     runs, there are no concurrent transactions, so in effect, all
       //     that is needed is to validate, writeback, and return true.
   }

  /**
   *  OrecELA_amd64 validation:
   *
   *    We only call this when in-flight, which means that we don't have any
   *    locks... This makes the code very simple, but it is still better to not
   *    inline it.
   */
  void validate(TxThread* tx)
  {
      foreach (OrecList, i, tx->r_orecs)
          // abort if orec locked, or if unlocked but timestamp too new
          if ((*i)->v.all > tx->start_time)
              tx->tmabort();
  }

  /**
   *  Switch to OrecELA_amd64:
   *
   *    The timestamp must be >= the maximum value of any orec.  Some algs use
   *    timestamp as a zero-one mutex.  If they do, then they back up the
   *    timestamp first, in timestamp_max.
   */
  void onSwitchTo()
  {
  }
}

// -----------------------------------------------------------------------------
// Register initialization as declaratively as possible.
// -----------------------------------------------------------------------------
/*
#define FOREACH_ORECLAZY(MACRO)               \
    MACRO(OrecELA_amd64, HyperAggressiveCM)          \
    MACRO(OrecELA_amd64Hour, HourglassCM)            \
    MACRO(OrecELA_amd64Backoff, BackoffCM)           \
    MACRO(OrecELA_amd64HB, HourglassBackoffCM)
*/
#define FOREACH_ORECLAZY(MACRO)                 \
    MACRO(OrecELA_amd64, HyperAggressiveCM)

#define INIT_ORECLAZY(ID, CM)                           \
    template <>                                         \
    void initTM<ID>()                                   \
    {                                                   \
        OrecELA_amd64_Generic<CM>::Initialize(ID, #ID); \
    }

namespace stm {
  FOREACH_ORECLAZY(INIT_ORECLAZY)
}
