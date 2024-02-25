import cocotb
import json
import os
import shutil
import subprocess

from pathlib import Path
from cocotb.clock import Clock
from cocotb.regression import TestFactory
from cocotb.result import SimTimeoutError
from cocotb.runner import get_runner, get_results
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb.triggers import Timer

import sys

p = Path.cwd() / '..' / 'common' / 'python'
sys.path.append(str(p))
import riscv_binary_utils

# directory where our simulator will compile our tests + code
SIM_BUILD_DIR = "sim_build"

# temporary file used to hold assembler output
TEMP_MACHINE_CODE_FILE = ".tmp.riscv.o"

# offset to map from standard Linux/ELF addresses to what our processor's memory uses
BIN_2_MEMORY_ADDRESS_OFFSET = 0x80000000

# assembler program
ASSEMBLER = 'riscv64-unknown-elf-as'

# readelf program
READELF = 'riscv64-unknown-elf-readelf'

RISCV_TESTS_PATH = Path('../../riscv-tests/isa')
RISCV_BENCHMARKS_PATH = Path('../../riscv-tests/benchmarks')

TIMEOUT_CYCLES = 1_000

def asm(dut, assemblyCode):
    """Assembles the given RISC-V code, returning the machine code as a list of numbers"""

    # avoid assembler warning about missing trailing newline
    if not assemblyCode.endswith('\n'):
        assemblyCode += '\n'
        pass

    # Use subprocess to run the assembler command
    command = [ASSEMBLER, "-march=rv32im", "-o", TEMP_MACHINE_CODE_FILE]
    process = subprocess.run(command, input=assemblyCode, capture_output=True, text=True, check=False)
    if process.returncode != 0:
        dut._log.error(f"Error: {process.stderr}")
        process.check_returncode() # throws
        pass

    loadBinaryIntoMemory(dut, TEMP_MACHINE_CODE_FILE)

def loadBinaryIntoMemory(dut, binaryPath):
    """Read the given binary's sections, and load them into memory at the appropriate addresses."""
    
    sectionInfo = riscv_binary_utils.getSectionInfo(binaryPath)
    #dut._log.info(sectionInfo)
    sectionsToLoad = ['.text.init','.text','.text.startup','.data','.tohost','.rodata','.rodata.str1.4','.sbss','.bss','.tbss']

    for sectionName in sectionsToLoad:
        if sectionName not in sectionInfo:
            continue
        offset = sectionInfo[sectionName]['offset']
        length = sectionInfo[sectionName]['size']
        words = riscv_binary_utils.extractDataFromBinary(binaryPath, offset, length + (length % 4))
        memBaseAddr = sectionInfo[sectionName]['address']
        if memBaseAddr >= BIN_2_MEMORY_ADDRESS_OFFSET:
            memBaseAddr -= BIN_2_MEMORY_ADDRESS_OFFSET
            pass
        memBaseAddr >>= 2 # convert to word address
        dut._log.info(f"loading {sectionName} section ({len(words)} words) into memory starting at 0x{memBaseAddr:x}")
        for i in range(len(words)):
            dut.mem.mem[memBaseAddr + i].value = words[i]
            pass
        pass
    pass


def oneTimeSetup():
    """This runs once, before any of the tests. Performs global setup."""

    # check that tools are accessible
    assert shutil.which(ASSEMBLER) is not None, f"Couldn't find assembler program {ASSEMBLER}"
    assert shutil.which(READELF) is not None, f"Couldn't find readelf program {READELF}"
    assert RISCV_TESTS_PATH.relative_to('..').exists(), f"Couldn't read riscv-tests from {RISCV_TESTS_PATH}"
    pass

async def memClock(dut):
    # pre-construct triggers for performance
    high_time = Timer(2, units="ns")
    low_time = Timer(2, units="ns")
    await Timer(1, units="ns") # phase shift by 90°
    while True:
        dut.clock_mem.value = 1
        await high_time
        dut.clock_mem.value = 0
        await low_time
        pass
    pass

async def preTestSetup(dut):
    """Setup the DUT. MUST be called at the start of EACH test."""
    # Create processor clock
    proc_clock = Clock(dut.clock_proc, 4, units="ns")
    # Start the clocks
    cocotb.start_soon(proc_clock.start(start_high=True))
    cocotb.start_soon(memClock(dut))
    # wait for first rising edge
    await RisingEdge(dut.clock_proc)

    # raise `rst` signal for one rising edge
    dut.rst.value = 1
    await ClockCycles(dut.clock_proc, 2)
    # lower `rst` signal
    dut.rst.value = 0
    # design should be reset now
    return

def runCocotbTests(pytestconfig):
    """setup cocotb tests, based on https://docs.cocotb.org/en/stable/runner.html"""

    hdl_toplevel_lang = os.getenv("HDL_TOPLEVEL_LANG", "verilog")
    sim = os.getenv("SIM", "verilator")
    proj_path = Path(__file__).resolve().parent
    assert hdl_toplevel_lang == "verilog"
    verilog_sources = [proj_path / "DatapathSingleCycle.sv" ]
    toplevel_module = "RiscvProcessor"

    pointsEarned = 0
    try:
        runr = get_runner(sim)
        runr.build(
            verilog_sources=verilog_sources,
            vhdl_sources=[],
            hdl_toplevel=toplevel_module,
            includes=[proj_path],
            build_dir=SIM_BUILD_DIR,
            always=True,
            # NB: --trace-max-array must be the size of the memory (in 4B words) for memory to appear in the waveforms
            build_args=['--assert','--trace','--trace-fst','--trace-structs','--trace-max-array',str(2**18)]
        )

        oneTimeSetup()

        runr.test(
            seed=12345,
            waves=True,
            hdl_toplevel=toplevel_module, 
            test_module=Path(__file__).stem, # use tests from this file
            testcase=pytestconfig.option.tests, # filter tests via the `--tests` command-line flag
        )
    finally:
        total_failed = get_results(Path(SIM_BUILD_DIR,'runCocotbTests.results.xml'))
        # 1 point per test
        pointsEarned += total_failed[0] - total_failed[1]
        pointsPossible = total_failed[0]     
        points = { 'pointsEarned': pointsEarned, 'pointsPossible': pointsPossible }
        with open('points.json', 'w') as f:
            json.dump(points, f, indent=2)
            pass
        pass


if __name__ == "__main__":
    runCocotbTests()
    pass



########################
## TEST CASES GO HERE ##
########################

async def check(dut, reg, val, msg=""):
    await ClockCycles(dut.clock_proc, 1)
    assert dut.datapath.rf.regs[reg].value == val, msg

@cocotb.test()
async def test3A(dut):
    "my own tests"
    asm(dut, '''lui x1, 0x12345
        addi x1, x1, 0x678
        addi x5, zero, 0xff
        and x1, x1, x5
        ''')
    await preTestSetup(dut)

    await ClockCycles(dut.clock_proc, 1)
    await check(dut, 1, 0x12345000, "failed lui")
    await check(dut, 1, 0x12345678, "failed addi")
    await check(dut, 5, 0xff, "failed addi 2")
    await check(dut, 1, 0x78, "failed and")
    #await check(dut, 1, 0xff, "failed addi 2")
    #await check(dut, 5, 1, "failed slti")
    #await check(dut, 5, 1, "failed sltiu")
    #await check(dut, 5, 0xffffff00, "failed xori")
#    await check(dut, 5, 0xfffff8ff, "failed ori")
 #   await check(dut, 5, 0x5, "failed andi")
  #  await check(dut, 5, 0xff0, "failed slli")
   # await check(dut, 5, 0xf, "failed srli")
    #await check(dut, 1, 0xffffffff, "failed addi 3")
#    await check(dit, 5, 0xffffffff, "failed srai")

    pass


