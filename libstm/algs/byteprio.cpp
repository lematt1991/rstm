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
 *  ByteEager Implementation
 *
 *    This is a good-faith implementation of the TLRW algorithm by Dice and
 *    Shavit, from SPAA 2010.  We use bytelocks, eager acquire, and in-place
 *    update, with timeout for deadlock avoidance.
 */

/**
 * Things to consier:
 *
 *   - Make priority a float -- num_aborts + (thread_id / (num_threads + 1))
 *           - this way we can systematically break ties and avoid livelock
 *           - We won't be able to acquire locks with this value, but we could
 *             still look it up given the offset of the bytelock
 */

#include "../profiling.hpp"
#include "algs.hpp"

using stm::UNRECOVERABLE;
using stm::TxThread;
using stm::ByteLockList;
using stm::bytelock_t;
using stm::get_bytelock;
using stm::WriteSet;
using stm::WriteSetEntry;


#define GET_WR_PRIO(x) (x & 0xFFFF)
#define GET_WR_ID(x) (x & 0xFFFF0000)
#define MK_LOCK_VAL(id, prio) ((prio << 16) | id)

#define RUNNING    1u
#define ABORTED    2u
#define COMMITTING 3u
/**
 *  Declare the functions that we're going to implement, so that we can avoid
 *  circular dependencies.
 */
namespace {
    struct BytePrio
    {
	static TM_FASTCALL bool begin(TxThread*);
	static TM_FASTCALL void* read_ro(STM_READ_SIG(,,));
	static TM_FASTCALL void* read_rw(STM_READ_SIG(,,));
	static TM_FASTCALL void write_ro(STM_WRITE_SIG(,,,));
	static TM_FASTCALL void write_rw(STM_WRITE_SIG(,,,));
	static TM_FASTCALL void commit_ro(TxThread*);
	static TM_FASTCALL void commit_rw(TxThread*);

	static stm::scope_t* rollback(STM_ROLLBACK_SIG(,,));
	static bool irrevoc(TxThread*);
	static void onSwitchTo();
    };

    /**
     *  These defines are for tuning backoff behavior
     */
#if defined(STM_CPU_SPARC)
#  define READ_TIMEOUT        32
#  define ACQUIRE_TIMEOUT     128
#  define DRAIN_TIMEOUT       1024
#else // STM_CPU_X86
#  define READ_TIMEOUT        32
#  define ACQUIRE_TIMEOUT     128
#  define DRAIN_TIMEOUT       256
#endif

    /**
     *  BytePrio begin:
     */
    bool
    BytePrio::begin(TxThread* tx)
    {
	tx->allocator.onTxBegin();
	tx->prio = 0;
	tx->alive = RUNNING;
	return false;
    }

    /**
     *  BytePrio commit (read-only):
     */
    void
    BytePrio::commit_ro(TxThread* tx)
    {
	if(!bcas32(&tx->alive, RUNNING, COMMITTING)){
	    tx->tmabort(tx);
	}

	// read-only... release read locks
	foreach (ByteLockList, i, tx->r_bytelocks)
	    (*i)->reader[tx->id-1] = 0;

	tx->r_bytelocks.reset();
	OnReadOnlyCommit(tx);
    }

    /**
     *  BytePrio commit (writing context):
     */
    void
    BytePrio::commit_rw(TxThread* tx)
    {
	if(!bcas32(&tx->alive, RUNNING, COMMITTING)){
	    tx->tmabort(tx);
	}

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
     * BytePrio read (read-only transaction)
     * If we attempt to acquire the read lock, but the write lock is already taken, 
     * we do the following:
     *
     * 1 - if we have higher priority:
     *      -- leave our byte set
     *      -- spin for READ_TIMEOUT iterations
     *      -- if it is still held, then abort the writer
     * 2 - if we have lower priority:
     *      -- spin for READ_TIMEOUT iterations
     *      -- if it is still held, then abort ourself
     */
    void*
    BytePrio::read_rw(STM_READ_SIG(tx,addr,))
    {
	if(tx->alive == ABORTED){
	    tx->tmabort(tx);
	}
      
	uint32_t tries = 0;
	bytelock_t* lock = get_bytelock(addr);

	//write lock already acquired
	if(GET_WR_PRIO(lock->owner) == tx->id){ 
	    WriteSetEntry log(STM_WRITE_SET_ENTRY(addr, NULL, mask));
	    if(tx->writes.find(log))  //did we acquire the lock for this address?
		return log.val;
	    return *addr;  //acquired lock for another address that hashes to this bytelock
	}

	if (lock->reader[tx->id-1] == 1) //do I have a read lock?
	    return *addr;

	tx->r_bytelocks.insert(lock);  //record bytelock

	// now try to get a read lock
	while (true) {
	    lock->set_read_byte_val(tx->id-1, tx->prio); //mark reader byte

	    // if nobody has the write lock, we're done
	    if (__builtin_expect(lock->owner == 0, true))
		return *addr;

	    while (lock->owner != 0) {
		if (++tries > READ_TIMEOUT){
		    uint32_t owner = lock->owner;
		    //writer has higher priority, I'll abort
		    if(owner > MK_WR_PRIO(tx->id, tx->prio)){
			tx->tmabort(tx);
		    }
		    //I have higher priority, so force the writer to abort
		    atomicswap32(&stm::threads[GET_WR_ID(owner)]->alive, ABORTED);
		    if(lock->owner == owner){
			return *addr;
		    }

		    //another writer locked it (or it's unlocked), so do the check again
		    tries = 0;
		    break;
		}
	    }
	}
    }

    void* BytePrio::read_ro(STM_READ_SIG(tx,addr,)){
	return BytePrio::read_rw(tx,addr);
    }

    /**
     *  BytePrio write (writing context)
     */
    void
    BytePrio::write_rw(STM_WRITE_SIG(tx,addr,val,mask))
    {
	if(tx->alive == ABORTED){
	    tx->tmabort(tx);  //someone aborted us
	}
      
	uint32_t tries = 0;
	bytelock_t* lock = get_bytelock(addr);

	// If I have the write lock, buffer this write and return
	if (lock->owner == tx->id) {         
	    tx->writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
	    return;
	}

	uint32_t lock_val = MK_LOCK_VAL(tx->id, tx->prio);	
	// get the write lock, with timeout
	while (!bcas32(&(lock->owner), 0u, tx->id)){
	    if (++tries > ACQUIRE_TIMEOUT){
		uint32_t owner = lock->owner;
		//use thread ID to break ties
		if(GET_WR_PRIO(owner) < tx->prio || (GET_WR_PRIO(owner) == tx->prio && GET_WR_ID(owner) < tx->id)){
		    if(!bcas32(&stm::threads[GET_WR_ID(owner)]->alive, RUNNING, ABORTED))
			continue; //they are either committing, or they were aborted by someone else
		    if(!bcas32(&lock->owner, owner, lock_val))
			continue; //someone else stole the lock, or they unlocked it.  Should we reset tries?
		    
		    tx->w_bytelocks.insert(lock);
		    lock->reader[tx->id-1] = 0;
		    tx->writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
		    OnFirstWrite(tx, read_rw, write_rw, commit_rw);
		    //no need to check for readers since we stole this from a writer
		    return;
		}
		tx->tmabort(tx);
	    }
	}
      
	// log the lock, drop any read locks I have
	tx->w_bytelocks.insert(lock);
	lock->reader[tx->id-1] = 0;

	// wait (with timeout) for readers to drain out
	// if we timeout but have higher priority than ALL readers, abort them all
	// and continue 
	// (read 4 bytelocks at a time)
	volatile uint32_t* lock_alias = (volatile uint32_t*)&lock->reader[0];
	for (int i = 0; i < BYTELOCK_READERS / 4; ++i) {
	    tries = 0;
	    while (lock_alias[i] != 0)
		if (++tries > DRAIN_TIMEOUT){
		    for(int j = i * 4; j < BYTELOCK_READERS; j++){
			if(lock->reader[j] > tx->prio){
			    tx->tmabort(tx);  //a reader has higher priority than me
			}
		    }
		    //kill all readers
		    for(int j = i * 4; j < BYTELOCK_READERS; j++){
			if(lock->reader[j] != 0){
			    stm::threads[j]->alive = ABORTED;
			}
		    }
		    //buffer write
		    tx->writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
		    return;
		}
	}

	//buffer write
	tx->writes.insert(WriteSetEntry(STM_WRITE_SET_ENTRY(addr, val, mask)));
    }

    /**
     *  BytePrio write (read-only context)
     */
    void
    BytePrio::write_ro(STM_WRITE_SIG(tx,addr,val,mask))
    {
	write_rw(tx, addr, val);
	OnFirstWrite(tx, read_rw, write_rw, commit_rw);
    }
    
    /**
     *  BytePrio unwinder:
     */
    stm::scope_t*
    BytePrio::rollback(STM_ROLLBACK_SIG(tx, except, len))
    {
	PreRollback(tx);

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

	return PostRollback(tx, read_ro, write_ro, commit_ro);
    }

    /** 
     *  BytePrio in-flight irrevocability:
     */
    bool BytePrio::irrevoc(TxThread*)
    {
	return false;
    }

    /**
     *  Switch to BytePrio:
     */
    void BytePrio::onSwitchTo() {
    }
}

namespace stm {
    /**
     *  BytePrio initialization
     */
    template<>
    void initTM<BytePrio>()
    {
	// set the name
	stms[BytePrio].name      = "BytePrio";

	// set the pointers
	stms[BytePrio].begin     = ::BytePrio::begin;
	stms[BytePrio].commit    = ::BytePrio::commit_ro;
	stms[BytePrio].read      = ::BytePrio::read_ro;
	stms[BytePrio].write     = ::BytePrio::write_ro;
	stms[BytePrio].rollback  = ::BytePrio::rollback;
	stms[BytePrio].irrevoc   = ::BytePrio::irrevoc;
	stms[BytePrio].switcher  = ::BytePrio::onSwitchTo;
	stms[BytePrio].privatization_safe = true;
    }
}
