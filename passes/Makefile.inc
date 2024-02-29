include $(ROOT)/Makefile.inc

INSTALL_DIR = $(ROOT)/bin

ARCH ?= native

ifeq "$(LLVM_DIR)" ""
  LLVM_CONFIG ?= llvm-config
  LLVM_PREFIX = $(shell $(LLVM_CONFIG) --prefix)
else
  LLVM_PREFIX=$(shell readlink -f $(LLVM_DIR))
  LLVM_CONFIG = $(LLVM_PREFIX)/bin/llvm-config
endif

$(info [+] LLVM prefix at $(LLVM_PREFIX))
$(info [+] LLVM config at $(LLVM_CONFIG))

LLVMVER  = $(shell $(LLVM_CONFIG) --version 2>/dev/null | sed 's/git//' | sed 's/svn//' )
ifeq "$(LLVMVER)" ""
  $(warning [!] llvm-config not found!)
endif

LLVM_BINDIR = $(shell $(LLVM_CONFIG) --bindir 2>/dev/null)
LLVM_LIBDIR = $(shell $(LLVM_CONFIG) --libdir 2>/dev/null)
LLVM_INCDIR = $(shell $(LLVM_CONFIG) --includedir 2>/dev/null)
LLVM_STDCXX = gnu++11

LLVM_NEW_API = $(shell $(LLVM_CONFIG) --version 2>/dev/null | egrep -q '^1[0-9]' && echo 1 || echo 0 )
ifeq "$(LLVM_NEW_API)" "1"
  $(info [+] detected llvm 10+, enabling c++14)
  LLVM_STDCXX = c++14
endif

CXX        = $(LLVM_BINDIR)/clang++

CXXFLAGS   += `$(LLVM_CONFIG) --cxxflags` -g -fPIC -Wno-long-long -Wall -W -Wno-unused-parameter -Wwrite-strings -Wno-unknown-warning-option -DHAVE_EXCEPTIONS=0 -march=$(ARCH)
LDFLAGS    += `$(LLVM_CONFIG) --ldflags` -L$(LLVM_LIBDIR)

$(info [+] CXX = $(CXX))

PASSLIBNAME =$(PASSNAME).so

HEADERS += $(wildcard ../include/common/*.h) $(wildcard ../include/$(PASSNAME)/*.h)

INCLUDES += -I../include/common -I../include/$(PASSNAME)

all: $(PASSLIBNAME)

$(PASSLIBNAME): $(OBJS)
	$(QUIET) $(ECHO) "  [LINK] $@"
	$(CXX) -std=$(LLVM_STDCXX) $(CXXFLAGS) -shared -o $@ $(CPPS) $(OBJS) $(LDFLAGS) $(LIBS)

%.o: %.cpp $(HEADERS)
	$(QUIET) $(ECHO)  "  [C++] $<"
	$(CXX) -std=$(LLVM_STDCXX) $(CXXFLAGS) $(INCLUDES) -c -o $@ $<

install: $(INSTALL_DIR)/$(PASSLIBNAME)

$(INSTALL_DIR)/$(PASSLIBNAME): $(PASSLIBNAME)
	$(QUIET) $(ECHO) "  [INSTALL] $< -> $@"
	install -c -D -m 744 $? $@

clean:
	$(QUIET) $(ECHO) "  [RM] $(OBJS) $(PASSLIBNAME)"
	rm -f $(OBJS) $(PASSLIBNAME) $(INSTALL_DIR)/$(PASSLIBNAME)
