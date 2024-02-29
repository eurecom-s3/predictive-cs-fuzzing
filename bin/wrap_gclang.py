#!/usr/bin/env python3

import subprocess
import shutil
import json
import sys
import os

import errno
from hashlib import sha256
from tempfile import gettempdir
from time import time, sleep

class ILockException(Exception):
    pass

class ILock(object):
    def __init__(self, name, timeout=None, check_interval=0.25, reentrant=False, lock_directory=None):
        self._timeout = timeout if timeout is not None else 10 ** 8
        self._check_interval = check_interval

        lock_directory = gettempdir() if lock_directory is None else lock_directory
        unique_token = sha256(name.encode()).hexdigest()
        self._filepath = os.path.join(lock_directory, 'ilock-' + unique_token + '.lock')

        self._reentrant = reentrant

        self._enter_count = 0

    def lock(self):
        import portalocker
  
        if self._enter_count > 0:
            if self._reentrant:
                self._enter_count += 1
                return self
            raise ILockException('Trying re-enter a non-reentrant lock')

        current_time = call_time = time()
        while call_time + self._timeout >= current_time:
            self._lockfile = open(self._filepath, 'w')
            try:
                portalocker.lock(self._lockfile, portalocker.constants.LOCK_NB | portalocker.constants.LOCK_EX)
                self._enter_count = 1
                return self
            except portalocker.exceptions.LockException:
                pass

            current_time = time()
            check_interval = self._check_interval if self._timeout > self._check_interval else self._timeout
            sleep(check_interval)

        raise ILockException('Timeout was reached')

    def __enter__(self):
        return self.lock()

    def unlock(self):
        self._enter_count -= 1

        if self._enter_count > 0:
            return

        if sys.platform.startswith('linux'):
            # In Linux you can delete a locked file
            os.unlink(self._filepath)

        self._lockfile.close()

        if sys.platform == 'win32':
            # In Windows you need to unlock a file before deletion
            try:
                os.remove(self._filepath)
            except WindowsError as e:
                # Mute exception in case an access was already acquired (EACCES)
                #  and in more rare case when it was even already released and file was deleted (ENOENT)
                if e.errno not in [errno.EACCES, errno.ENOENT]:
                    raise

    def __exit__(self, exc_type, exc_val, exc_tb):
        return self.unlock()

SOURCE_EXTENSIONS = ('.c', '.cc', '.cpp', '.h',
                     '.hpp')
FILTER_EXTENSIONS = ('.c', '.cc', '.cpp', '.h',
                     '.hpp', '.o', '.obj', '.a', '.la')

script_dir = os.path.dirname(os.path.realpath(os.path.abspath(__file__)))

is_cxx = "++" in sys.argv[0]

is_debug = os.getenv("WRAP_GCLANG_DEBUG") is not None
keep_symbols = os.getenv("CGC_KEEP_SYMBOLS") is not None
compiler_path = os.getenv("LLVM_COMPILER_PATH")
benchmark = os.getenv("BENCHMARK")
fuzzer = os.getenv("FUZZER")
experiment = os.getenv("EXPERIMENT", 'noexp')

fuzz_programs = []
fuzz_target = os.getenv("FUZZ_TARGET")
# ffmpeg_ffmpeg_demuxer_fuzzer first compiles `tools/target_dem_fuzzer` and then moves it to /out/ffmpeg_DEMUXER_fuzzer
if fuzz_target is not None and benchmark == 'ffmpeg_ffmpeg_demuxer_fuzzer' and  'ffmpeg_DEMUXER_fuzzer' in fuzz_target:
    fuzz_target = fuzz_target.replace('ffmpeg_DEMUXER_fuzzer', 'target_dem_fuzzer')

if fuzz_target is not None:
    fuzz_programs.append(os.path.basename(fuzz_target))
if os.getenv("FUZZ_PROGRAMS") is not None:
    fuzz_programs += list(map(lambda x: x.strip(), os.getenv("FUZZ_PROGRAMS").split(",")))

configure_only = os.getenv('WLLVM_CONFIGURE_ONLY')

def get_string(s):
    res = ''
    for ss in s:
        res += chr(ss - 1)
    return res

def get_stats(filename):
    if os.getenv("OPT_PATH"):
        opt_name = os.environ["OPT_PATH"]
    elif compiler_path is not None:
        opt_name = os.path.join(compiler_path, "opt")
    else:
        opt_name = "opt"
    out = subprocess.check_output("%s -load=%s/func-stats.so -func-stats %s -o /dev/null" % (opt_name, script_dir, filename), shell=True).decode()
    assert('Num functions: ' in out and 'Num BBs      : ' in out and 'AFL edges    : ' in out)
    num_funcs = int(out.split('Num functions: ')[1].split('\n')[0])
    num_bb    = int(out.split('Num BBs      : ')[1].split('\n')[0])
    afl_edges = int(out.split('AFL edges    : ')[1].split('\n')[0])
    return num_funcs, num_bb, afl_edges

def get_filesize(file):
    try:
        return os.path.getsize(file)
    except OSError:
        return 0

def log_stats(filename):
    strategy = os.getenv("CGC_STRATEGY")
    type = "icp" if os.getenv("FORCE_ICP") else "noicp"
    bc = os.path.basename(filename)
    num_funcs, num_bb, afl_edges = get_stats(filename)
    filesize = get_filesize(filename)
    data = 'stats,type=%s experiment="%s",benchmark="%s",fuzzer="%s",bc="%s",strategy="%s",num_functions=%di,num_bb=%di,afl_edges=%di,size=%di' % (type, experiment, benchmark, fuzzer, bc, strategy, num_funcs, num_bb, afl_edges, filesize)

def log_msg(filename, msg):
    strategy = os.getenv("CGC_STRATEGY")
    type = "icp" if os.getenv("FORCE_ICP") else "noicp"
    bc = os.path.basename(filename)
    data = 'msgs,type=%s experiment="%s",benchmark="%s",fuzzer="%s",file="%s",strategy="%s",msg="%s"' % (type, experiment, benchmark, fuzzer, bc, strategy, msg)

# gclang does not forward optimization flags to the linking step, so -fsanitize=object-size
# will lead to a warning on missing optimizations when compiling.
# This is usually safe, but will make fail some ./configure scripts
def filter_objsan(args):
    for i, arg in enumerate(args):
        if arg.startswith('-fsanitize='):
            args[i] = args[i].replace('object-size,', '') # if not last
            args[i] = args[i].replace(',object-size', '') # if last
    if '-fsanitize=object-size' in args: args.remove('-fsanitize=object-size') # if alone

def gclang_exec(args, capture_output=False):
    if os.getenv("GCLANG_PATH"):
        cc_name = os.environ["GCLANG_PATH"]
    else:
        cc_name = "gclang"
    if is_cxx:
        if os.getenv("GCLANGXX_PATH"):
            cc_name = os.environ["GCLANGXX_PATH"]
        else:
            cc_name = "gclang++"
    argv = [cc_name] + args
    if is_debug:
        print(" ".join(argv), file=sys.stderr)
    if capture_output:
        return subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    else:
        return subprocess.run(argv)


def cc_exec(args, capture_output=False):
    if os.getenv("REAL_CC_PATH"):
        cc_name = os.environ["REAL_CC_PATH"]
    elif compiler_path is not None:
        cc_name = os.path.join(compiler_path, "clang")
    else:
        cc_name = "clang"
    if is_cxx:
        if os.getenv("REAL_CXX_PATH"):
            cc_name = os.environ["REAL_CXX_PATH"]
        elif compiler_path is not None:
            cc_name = os.path.join(compiler_path, "clang++")
        else:
            cc_name = "clang++"
    argv = [cc_name] + args
    if is_debug:
        print(" ".join(argv), file=sys.stderr)
    if capture_output:
        return subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    else:
        return subprocess.run(argv)


def opt_exec(args, capture_output=False, check_ret=True, wrapper_cmd=None, save_output=False, save_input=False):
    if os.getenv("OPT_PATH"):
        cc_name = os.environ["OPT_PATH"]
    elif compiler_path is not None:
        cc_name = os.path.join(compiler_path, "opt")
    else:
        cc_name = "opt"
    argv = [cc_name] + args
    if wrapper_cmd is not None:
        argv = wrapper_cmd + argv
    if is_debug:
        print(" ".join(argv), file=sys.stderr)
    # ugly docker debug
    if os.path.exists('/host_tmp'):
        os.system("cp %s /host_tmp" % args[-1])
    if save_input:
        os.system('cp %s %s' % (argv[-1], os.getenv('OUT', '/tmp/')))
    if capture_output:
        ret = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    else:
        ret = subprocess.run(argv)
    if check_ret:
        assert(ret.returncode == 0)
    # ugly docker debug
    if ret.returncode == 0 and os.path.exists('/host_tmp'):
        os.system("cp %s /host_tmp" % args[-2])
    if save_output:
        os.system('cp %s %s' % (argv[-2], os.getenv('OUT', '/tmp/')))
    return ret

def extract_exec(args, capture_output=False, check_ret=True):
    if os.getenv("EXTRACT_PATH"):
        ext_name = os.environ["EXTRACT_PATH"]
    elif compiler_path is not None:
        ext_name = os.path.join(compiler_path, "llvm-extract")
    else:
        ext_name = "llvm-extract"
    argv = [ext_name] + args
    if is_debug:
        print(" ".join(argv), file=sys.stderr)
    if capture_output:
        ret = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    else:
        ret = subprocess.run(argv)
    if check_ret:
        assert(ret.returncode == 0)
    return ret

def link_exec(args, capture_output=False, check_ret=True):
    if os.getenv("LINK_PATH"):
        tool_name = os.environ["LINK_PATH"]
    elif compiler_path is not None:
        tool_name = os.path.join(compiler_path, "llvm-link")
    else:
        tool_name = "llvm-link"
    argv = [tool_name] + args
    if is_debug:
        print(" ".join(argv), file=sys.stderr)
    if capture_output:
        ret = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    else:
        ret = subprocess.run(argv)
    if check_ret:
        assert(ret.returncode == 0)
    return ret

def strip_exec(args):
    if os.getenv("STRIP_PATH"):
        tool_name = os.environ["STRIP_PATH"]
    elif compiler_path is not None:
        tool_name = os.path.join(compiler_path, "llvm-strip")
    else:
        tool_name = "llvm-strip"
    argv = [tool_name] + args
    subprocess.check_call(argv, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def get_bc(filename, bc_filename=None, strict_mode=False, capture_output=False):
    if bc_filename is None:
        bc_filename = filename + '.bc'
    if os.getenv("GETBC_PATH"):
        cc_name = os.environ["GETBC_PATH"]
    else:
        cc_name = "get-bc"
    argv = ['get-bc', '-b', '-o', bc_filename]
    if strict_mode:
        argv.append('-S')
    argv.append(filename)
    if is_debug:
        print(" ".join(argv), file=sys.stderr)
    if capture_output:
        return subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    else:
        return subprocess.run(argv)


def common_opts():
    return [
        # BEWARE: we need to insert debug info to be able to properly extract libraries
        # based on the file path
        "-g",
        "-fno-function-sections",
        '-fno-unique-section-names',
        "-funroll-loops",
        # "-fno-discard-value-names",
    ]


def cc_mode():
    old_args = sys.argv[1:]
    filter_objsan(old_args)

    args = common_opts()
    have_o = False
    for arg in old_args:
        if arg.startswith('-O'):
            have_o = True
        if not arg == '-ffunction-sections':
            args.append(arg)
    if not have_o:
        args = ['-O3'] + args

    assert(gclang_exec(args).returncode == 0)

def add_afl_symbols(outfile):
    subprocess.check_call("echo '__afl_persistent_loop' >> %s" % outfile, shell=True)
    subprocess.check_call("echo '__afl_manual_init' >> %s" % outfile, shell=True)
    subprocess.check_call("echo '__afl_fuzz_len' >> %s" % outfile, shell=True)
    subprocess.check_call("echo '__afl_fuzz_ptr' >> %s" % outfile, shell=True)

def gen_whitelist():
    bench_name = os.getenv("BENCHMARK")
    assert bench_name
    # Get the project name from the benchmark name
    proj_name = bench_name.split("_")[0].split("-")[0]
    fuzzbench_src = os.getenv("SRC")
    assert fuzzbench_src
    # match any path containing the project name, and strictly the SRC directory
    return "{},^{}$".format(proj_name, fuzzbench_src)

def get_cache_size(index):
    cache_size = open('/sys/devices/system/cpu/cpu0/cache/index{}/size'.format(index)).read().strip()
    if cache_size[-1] == 'K' or cache_size[-1] == 'k':
        return int(cache_size[:-1]) * 1024
    elif cache_size[-1] == 'M' or cache_size[-1] == 'm':
        return int(cache_size[:-1]) * 1024 * 1024
    else:
        # Do not expect Gb sized caches in the near future :(
        assert (cache_size.isdecimal())
        return int(cache_size)

def get_map_limit():
    if os.getenv("CGC_MAXMAP") is None:
        return get_cache_size(os.getenv("CGC_CACHEDMAP", "2"))
    else:
        return int(os.getenv("CGC_MAXMAP"))

# gclang fails extracting the bitcode for source files that are inside a linker group
# so extract them, plus extract also `-o output` if it is in the linker group
def fix_linker_groups(args):
    last_group = 0
    # search all occurrences, a ValueError will end the search
    while True:
        try:
            #search for linker groups
            last_group = args.index('-Wl,--start-group', last_group)
            end_group = args.index('-Wl,--end-group', last_group)
            idx = last_group + 1
            while idx < end_group:
                arg = args[idx]
                if arg.endswith(SOURCE_EXTENSIONS):
                    args.insert(last_group, args.pop(idx))
                    last_group += 1
                elif arg == '-o':
                    # pop both the `-o` and the param
                    args.insert(last_group, args.pop(idx))
                    args.insert(last_group+1, args.pop(idx+1))
                    last_group += 2
                else:
                    idx += 1
            last_group = end_group + 1

        except ValueError:
            return

def ld_mode():
    old_args = sys.argv[1:]
    filter_objsan(old_args)

    args = common_opts() + ['-Wl,--allow-multiple-definition']
    linker_args = common_opts() + [os.path.join(script_dir, 'aflpp-link-safe.o')]#, '-lrt', '-pthread']

    outname = None

    have_o = False
    opt_level = None
    have_std = []
    filtereds = []
    i = 0
    while i < len(old_args):
        if old_args[i].startswith('-O'):
            have_o = True
            opt_level = old_args[i]
        if old_args[i].startswith('-std='):
            have_std = [old_args[i]]
        if not old_args[i] == '-ffunction-sections':
            linker_args.append(old_args[i])
        if old_args[i] == '-o':
            outname = old_args[i + 1]
            linker_args.append(outname)
            args += [outname + '.final.bc.o', '-o', outname]
            i += 1
        elif not old_args[i].endswith(FILTER_EXTENSIONS):
            args.append(old_args[i])
        else:
            filtereds.append(old_args[i])
        i += 1
    if not have_o:
        args = ['-O3'] + args
        linker_args = ['-O3'] + linker_args
        opt_level = '-O3'

    if outname is None:
        outname = 'a.out'
        args += [outname + '.final.bc.o', '-o', outname]

    if len(fuzz_programs) > 0 and os.path.basename(outname) not in fuzz_programs:
        assert(gclang_exec(old_args + [os.path.join(script_dir, 'aflpp-link-safe.o')]).returncode == 0)
        return

    fix_linker_groups(linker_args)
    assert(gclang_exec(linker_args).returncode == 0)

    log_msg(benchmark, "start")
    assert(get_bc(outname, capture_output=True).returncode == 0)

    for fname in filtereds:
        orig_fname = fname
        if fname.startswith("-l:"):
            fname = fname[3:]
        if fname.endswith('.o') and get_bc(fname, strict_mode=True, capture_output=True).returncode != 0:
            args += [orig_fname] # reinclude in the link command
        # reinclude also libs/libsz.a needed by libs like `libhdf5` (in matio_matio_fuzzer it links the system libhdf5 for which bitcode is unavailable)
        elif fname.endswith('.a') and (get_bc(fname, strict_mode=True, capture_output=True).returncode != 0 or 'libs/libsz.a' in fname):
            args += [orig_fname] # reinclude in the link command

    # strip and log original size
    strip_exec(['--strip-all-gnu', outname])
    log_msg(benchmark, "orig_size: %d" % get_filesize(outname))

    ilock = None
    if os.getenv("WRAP_GCLANG_LOCK") is not None:
        ilock = ILock(os.getenv("WRAP_GCLANG_LOCK"))
        ilock.lock()

    input_fname = outname + '.bc'
    log_stats(input_fname)
    if os.getenv("NO_PASSES") is None:
        if os.getenv("NO_INTERNALIZE") is None and os.getenv("NO_INTERNALIZE1") is None:
            opt_exec(['-load=%s/dump-call-tree.so' % script_dir, '-dump-call-tree', '-call-tree-start=main', '-dump-tree-file=call-tree.log',
                      '-o', '/dev/null', outname + '.bc'])
            add_afl_symbols("call-tree.log")
            opt_exec(['-internalize', '-internalize-public-api-file=call-tree.log',
                      '-globaldce', '-o', outname + '.internalized.bc', input_fname])
            input_fname = outname + '.internalized.bc'
            log_stats(input_fname)
        if os.getenv("NO_EXTRACT") is None:
            whitelist = gen_whitelist()
            opt_exec(['-load=%s/dump-extlib.so' % script_dir, '-dump-extlib', '-dumpext-whitelist=%s' % whitelist,
                      '-dumpext-blacklist=third_party,third-party', '-dumpext-out=funcs.log',
                      '-o', input_fname, input_fname])
            functions_to_extract = open('funcs.log').read().strip()
            if len(functions_to_extract) > 0:
                # solidity has too many functions to extract, fix it
                if 'solidity' in benchmark:
                    fl = functions_to_extract.split(' ')
                    functions_to_extract1 = fl[:len(fl)//2]
                    functions_to_extract2 = fl[len(fl)//2:]
                    extract_exec(functions_to_extract1 + ['-o', 'lib1.bc', input_fname])
                    extract_exec(functions_to_extract2 + ['-o', 'lib2.bc', input_fname])
                    link_exec(['-o', 'lib.bc', 'lib1.bc', 'lib2.bc'])
                    extract_exec(functions_to_extract1 + [ '--delete', '-o', outname + '.extracted1.bc', input_fname])
                    extract_exec(functions_to_extract2 + [ '--delete', '-o', outname + '.extracted.bc', outname + '.extracted1.bc'])
                else:
                    extract_exec(functions_to_extract.split(' ') + ['-o', 'lib.bc', input_fname])
                    extract_exec(functions_to_extract.split(' ') + [ '--delete', '-o', outname + '.extracted.bc', input_fname])
                opt_exec([opt_level, '-loop-unroll', '-o', 'lib.bc', 'lib.bc'])
                input_fname = outname + '.extracted.bc'
                log_stats(input_fname)
        if os.getenv("FORCE_ICP"):
            opt_exec(['-load=%s/icp.so' % script_dir, '-icp', '-icp-fallback', '-icp-type', '-icp-type-opaque-ptrs=0',
                      '-icp-alias', '-stat=0', '-ander', '-modelConsts', '-o', outname + '.icp.bc', input_fname])
            input_fname = outname + '.icp.bc'
            log_stats(input_fname)
        if os.getenv("NO_CGC") is None:
            cgc_strategy = os.getenv("CGC_STRATEGY") if os.getenv("CGC_STRATEGY") is not None else 'dataflow'
            cgc_fill = "0" if os.getenv("CGC_NOFILL") else "1"
            scalarize = []
            sea_dependencies = []
            vectorize = []
            # split passes in two invocations, since it seems to avoid a crash with sqlite3 and sea-dsa which happens in misterious conditions (only docker, no valgrind)
            opt_exec([opt_level, '-loop-unroll'] + scalarize + [
                      '-load=%s/cgc-planner.so' % script_dir] + sea_dependencies + ['-o', outname + '.temp.bc', input_fname], save_output=True)
            input_fname = outname + '.temp.bc'
            log_stats(input_fname)

            if os.getenv("CGC_ONLY_PTR_EVAL") is not None:
                def ptr_eval(strategy):
                    ofile = '%s.txt' % strategy
                    opt_exec(['-load=%s/ptr-eval.so' % script_dir, '-ptr-eval', '-ptr-strategy=%s' % strategy, 
                        '-ptr-out=%s' % ofile, '-stat=0', '-modelConsts',
                        '-o', '/dev/null', input_fname], check_ret=False, 
                        wrapper_cmd=['/usr/bin/time', "-f", "%M", '-o', 'time_stats.txt'])
                    if os.path.exists('time_stats.txt'):
                        with open('time_stats.txt') as f:
                            max_mem = f.read().strip().replace('\n', ' ')
                            os.remove('time_stats.txt')
                    else:
                        max_mem = '-1'
                    
                    if os.path.exists(ofile):
                        with open(ofile) as f:
                            res = f.read()
                        os.remove(ofile)
                        return res + '|' + max_mem

                    else:
                        return ("%s: -1|-1|-1" % strategy) + '|' + max_mem

                log_msg(benchmark, ptr_eval('params'))
                log_msg(benchmark, ptr_eval('dataflowSea'))
                log_msg(benchmark, ptr_eval('dataflow'))
                
            if os.getenv("CGC_ONLY_CGC_EVAL") is not None:
                ret = opt_exec(['-load=%s/func-stats.so' % script_dir, '-func-stats', '-dump-graph',
                    '-o', '/dev/null', input_fname], check_ret=True, capture_output=True)
                with open('cgc.txt', 'w') as f:
                    f.write(ret.stdout.decode(errors='ignore'))
                
                out = subprocess.check_output(['python3', '%s/cgc.py' % script_dir, 'cgc.txt'])
                log_msg(benchmark, out.strip().decode(errors='ignore'))
                return

            opt_exec(['-load=%s/cgc-planner.so' % script_dir, '-cgc-planner', '-cgc-strategy=%s' % cgc_strategy, '-cgc-funcs=^main$', '-cgc-calls-treshold=50', '-stat=0', '-modelConsts'] + vectorize + 
                      ['-o', outname + '.lto.bc', input_fname])
            input_fname = outname + '.lto.bc'
            log_stats(input_fname)

            max_aflmap = get_map_limit()
            # if the libs have been extracted, set the max accordingly
            if os.getenv("NO_EXTRACT") is None and len(functions_to_extract) > 0:
                _, _, lib_edges = get_stats('lib.bc')
                _, _, cur_edges = get_stats(input_fname)
                max_aflmap -= lib_edges
                while cur_edges >= max_aflmap:
                    max_aflmap += get_map_limit()

            opt_exec(['-load=%s/cgc.so' % script_dir, '-cgc', '-cgc-clone-prefix=', '-cgc-max-aflmap=%d' % max_aflmap, '-cgc-fill=%s' % cgc_fill,
                      '-load=%s/dump-call-tree.so' % script_dir, '-dump-call-tree', '-call-tree-start=main', '-dump-tree-file=call-tree.log',
                      '-o', outname + '.cgc.bc', input_fname])
            input_fname = outname + '.cgc.bc'
            log_stats(input_fname)
        if os.getenv("FORCE_INTERNALIZE") is not None:
            add_afl_symbols("call-tree.log")
            opt_exec(['-internalize', '-internalize-public-api-file=call-tree.log', 
                      '-globaldce', '-o', outname + '.cgc.internalized.bc', input_fname])
            input_fname = outname + '.cgc.internalized.bc'
            log_stats(input_fname)

    if os.getenv("CGC_LOG_CALLS") is not None:
        opt_exec(['-load=%s/dump-calls.so' % script_dir, '-dump-calls', 
                '-o', outname + '.log.bc', input_fname])
        input_fname = outname + '.log.bc'
        log_stats(input_fname)

    if os.getenv("NO_PASSES") is None and os.getenv("NO_EXTRACT") is None and len(functions_to_extract) > 0:
        link_exec(['-o', outname + '.linked.bc', input_fname, 'lib.bc'])
        input_fname = outname + '.linked.bc'
        log_stats(input_fname)

    shutil.copy(input_fname, outname + '.final.bc')
    log_stats(outname + '.final.bc')

    assert(cc_exec(common_opts() + have_std + [opt_level] + [outname + '.final.bc', '-c', '-o', outname + '.final.bc.o']).returncode == 0)
    
    #if fuzz_target is not None and 'grok' in fuzz_target:
    #    if '-std=c++11' in args: args.remove('-std=c++11')
    #    args = ['-std=gnu++2a'] + args

    # this fixes a bug at the linking stage for exiv2: `__sancov_pcs has both ordered [...] and unordered [...] sections`
    # see https://github.com/rust-lang/rust/issues/53945 and https://github.com/google/oss-fuzz/pull/6288 for details
    if 'exiv2' in benchmark:
        args += ['-fuse-ld=gold']

    assert(cc_exec(args).returncode == 0)

    if not keep_symbols:
        # strip and log final size
        strip_exec(['--strip-all-gnu', outname])
    log_msg(benchmark, "final_size: %d" % get_filesize(outname))
    log_msg(benchmark, "end")

    # ugly docker debug
    if os.path.exists('/host_tmp'):
        os.system("cp %s /host_tmp" % (outname + '.final.bc'))
        os.system("cp %s /host_tmp" % outname)
    
    if ilock is not None:
        ilock.unlock()


def is_ld_mode():
    return not ("--version" in sys.argv or "--target-help" in sys.argv or
                "-c" in sys.argv or "-E" in sys.argv or "-S" in sys.argv or
                "-shared" in sys.argv)


if len(sys.argv) <= 1:
    cc_exec([])
elif is_ld_mode() and not configure_only:
    ld_mode()
else:
    cc_mode()
