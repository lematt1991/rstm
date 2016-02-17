/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

#include <stm/config.h>
#if defined(STM_CPU_SPARC)
#include <sys/types.h>
#endif

/**
 *  Step 1:
 *    Include the configuration code for the harness, and the API code.
 */

#include <iostream>
#include <api/api.hpp>
#include "bmconfig.hpp"

/**
 *  We provide the option to build the entire benchmark in a single
 *  source. The bmconfig.hpp include defines all of the important functions
 *  that are implemented in this file, and bmharness.cpp defines the
 *  execution infrastructure.
 */
#ifdef SINGLE_SOURCE_BUILD
#include "bmharness.cpp"
#endif

/**
 *  Step 2:
 *    Declare the data type that will be stress tested via this benchmark.
 *    Also provide any functions that will be needed to manipulate the data
 *    type.  Take care to avoid unnecessary indirection.
 */

int* matrix;

int ** local_mats;

/**
 *  Step 3:
 *    Declare an instance of the data type, and provide init, test, and verify
 *    functions
 */

/*** Initialize an array that we can use for our MCAS test */
void bench_init()
{
    matrix = (int*)malloc(CFG.elements * sizeof(int));

    local_mats = (int**)malloc(sizeof(int*));
    
    for(int i = 0; i < CFG.threads; i++){
	local_mats[i] = (int*)malloc(sizeof(int) * CFG.elements);
    }
}

/*** Run a bunch of random transactions */
void bench_test(uintptr_t id, uint32_t* seed)
{
    uint32_t loc[1024];
    int snapshot[1024];

    //determine the locations prior to the transaction
    for(uint32_t i = 0; i < CFG.ops; i++){
	uint32_t r = rand_r(seed) % CFG.elements;
	local_mats[id][r]++;
	loc[i] = r;
    }
    
    TM_BEGIN(atomic) {
        for (uint32_t i = 0; i < CFG.ops; ++i) {
            snapshot[i] = TM_READ(matrix[loc[i]]);
        }
        for (uint32_t i = 0; i < CFG.ops; ++i) {
            TM_WRITE(matrix[loc[i]], 1 + snapshot[i]);
        }
    } TM_END;
}

/*** Ensure the final state of the benchmark satisfies all invariants */
bool bench_verify() {
    
    for(int i = 0; i < CFG.threads; i++){
	for(int j = 0; j < CFG.ops; j++){
	    matrix[j] -= local_mats[i][j];
	}
    }

    bool passed = true;
    
    for(int i = 0; i < CFG.ops; i++){
	if(matrix[i] != 0){
	    printf("Nonzero entry (%d) at position %d\n", matrix[i], i);
	    passed = false;
	}
    }
    return passed;
}

/**
 *  Step 4:
 *    Include the code that has the main() function, and the code for creating
 *    threads and calling the three above-named functions.  Don't forget to
 *    provide an arg reparser.
 */

/*** Deal with special names that map to different M values */
void bench_reparse()
{
    if      (CFG.bmname == "")          CFG.bmname   = "ReadWriteN";
}
