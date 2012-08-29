#
#  Copyright (C) 2011
#  University of Rochester Department of Computer Science
#    and
#  Lehigh University Department of Computer Science and Engineering
# 
# License: Modified BSD
#          Please see the file LICENSE.RSTM for licensing information

#
# All of the platforms for which we have a common/PLATFORM.mk file are listed
# here, along with a (admittedly not so useful) build target that describes
# them all.  Including this at the top of any build target is a nice way to
# ensure that typing 'make' without a platform just spits out instructions
#

PLATFORMS = gcc_linux_ia32_dbg      gcc_linux_ia32_opt      \
            gcc_linux_amd64_dbg     gcc_linux_amd64_opt     \
            gcc_solaris_ia32_dbg    gcc_solaris_ia32_opt    \
            gcc_solaris_amd64_dbg   gcc_solaris_amd64_opt   \
            gcctm_solaris_ia32_dbg  gcctm_solaris_ia32_opt  \
            gcctm_solaris_amd64_dbg gcctm_solaris_amd64_opt \
	    gcc_linux_armv7_opt     gcc_linux_ia32_opt_pmu

info:
	@echo "You must specify your platform as the build target."
	@echo "Valid platforms are:"
	@echo "  gcc_linux_ia32_dbg"
	@echo "      library API, gcc, Linux, x86, 32-bit, -O0"
	@echo "  gcc_linux_ia32_opt"
	@echo "      library API, gcc, Linux, x86, 32-bit, -O3"
	@echo "  gcc_linux_amd64_dbg"
	@echo "      library API, gcc, Linux, x86, 64-bit, -O0"
	@echo "  gcc_linux_amd64_opt"
	@echo "      library API, gcc, Linux, x86, 64-bit, -O3"
	@echo "  gcc_solaris_ia32_dbg"
	@echo "      library API, gcc, Solaris, x86, 32-bit, -O0"
	@echo "  gcc_solaris_ia32_opt"
	@echo "      library API, gcc, Solaris, x86, 32-bit, -O0"
	@echo "  gcc_solaris_amd64_dbg"
	@echo "      library API, gcc, Solaris, x86, 64-bit, -O0"
	@echo "  gcc_solaris_amd64_opt"
	@echo "      library API, gcc, Solaris, x86, 64-bit, -O0"
	@echo "  gcctm_solaris_ia32_dbg"
	@echo "      gcctm API, gcc, Solaris, x86, 32-bit, -O0"
	@echo "  gcctm_solaris_ia32_opt"
	@echo "      gcctm API, gcc, Solaris, x86, 32-bit, -O3"
	@echo "  gcctm_solaris_amd64_dbg"
	@echo "      gcctm API, gcc, Solaris, x86, 64-bit, -O0"
	@echo "  gcctm_solaris_amd64_opt"
	@echo "      gcctm API, gcc, Solaris, x86, 64-bit, -O3"
	@echo "  gcc_linux_armv7_opt"
	@echo "      library API, gcc, Linux, ARM7, 32-bit, -O3"
	@echo "  gcc_linux_ia32_opt_pmu"
	@echo "      library API, gcc, Linux, x86, 32-bit, -O3, PMU support"