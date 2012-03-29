#
#  Copyright (C) 2011
#  University of Rochester Department of Computer Science
#    and
#  Lehigh University Department of Computer Science and Engineering
# 
# License: Modified BSD
#          Please see the file LICENSE.RSTM for licensing information
#

#
# This makefile is for building the RSTM libraries and benchmarks using
# library API, GCC, Linux, ia32, -O0
#
# Warning: This just handles platform configuration.  Everything else is
#          handled via per-folder Makefiles
#

#
# Compiler config
#
PLATFORM  = lib_gcc_linux_ia32_dbg
CXX       = g++
CC       ?= gcc
CXXFLAGS += -O0 -ggdb -m32 -march=native -mtune=native -msse2 -mfpmath=sse
LDFLAGS  += -lrt -lpthread -m32 
CFLAGS   += -m32
ASFLAGS  += -m32

#
# Options to pass to STM files
#
CXXFLAGS += -DSTM_API_LIB
CXXFLAGS += -DSTM_CC_GCC
CXXFLAGS += -DSTM_OS_LINUX
CXXFLAGS += -DSTM_CPU_X86
CXXFLAGS += -DSTM_BITS_32
CXXFLAGS += -DSTM_OPT_O0
CXXFLAGS += -DSTM_WS_WORDLOG