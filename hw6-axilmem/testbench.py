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
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles
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

TRACING_MODE = 'compare' # compare against the solution trace
#TRACING_MODE = None # don't compare against or generate a trace
#TRACING_MODE = 'generate' # generate a new trace (for staff only)

def asm(dut, assemblyCode):
    """Assembles the given RISC-V code, returning the machine code as a list of numbers"""

    # avoid assembler warning about missing trailing newline
    if not assemblyCode.endswith('\n'):
        assemblyCode += '\n'
        pass

    # Use subprocess to run the assembler command
    #command = [ASSEMBLER, "-march=rv32imzifencei", "-o", TEMP_MACHINE_CODE_FILE]
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
            dut.mem.mem_array[memBaseAddr + i].value = words[i]
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

async def preTestSetup(dut):
    """Setup the DUT. MUST be called at the start of EACH test."""
    # Create clock
    proc_clock = Clock(dut.clk, 4, units="ns")
    # Start the clocks
    cocotb.start_soon(proc_clock.start(start_high=True))
    # wait for first rising edge
    await RisingEdge(dut.clk)

    # raise `rst` signal for one rising edge
    dut.rst.value = 1
    await ClockCycles(dut.clk, 2)
    #await FallingEdge(dut.clk)
    # lower `rst` signal
    dut.rst.value = 0
    # design should be reset now

    # await ClockCycles(dut.clk, 1)

    return

def runCocotbTests(pytestconfig):
    """setup cocotb tests, based on https://docs.cocotb.org/en/stable/runner.html"""

    hdl_toplevel_lang = os.getenv("HDL_TOPLEVEL_LANG", "verilog")
    sim = os.getenv("SIM", "verilator")
    proj_path = Path(__file__).resolve().parent
    assert hdl_toplevel_lang == "verilog"
    verilog_sources = [ proj_path / "DatapathAxilMemory.sv" ]
    toplevel_module = "RiscvProcessor"

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
            build_args=['--assert','-Wall','-Wno-DECLFILENAME','--trace','--trace-fst','--trace-structs','--trace-max-array',str(2**18)]
        )

        oneTimeSetup()

        runr.test(
            seed=12345,
            waves=True,
            hdl_toplevel=toplevel_module, 
            test_module=Path(__file__).stem, # use tests from this file
            results_xml='axilmem_datapath.results.xml',
            testcase=pytestconfig.option.tests, # filter tests via the `--tests` command-line flag
        )
    finally:
        pointsEarned = 0
        pointsPossible = 0
        mem_path = Path(SIM_BUILD_DIR,'runCocotbTests.axilmem.results.xml')
        proc_path = Path(SIM_BUILD_DIR,'runCocotbTests.axilmem_datapath.results.xml')
        if mem_path.exists() and proc_path.exists():
            mem_total_failed = get_results(mem_path)
            proc_total_failed = get_results(proc_path)
            # 1 point per test
            pointsEarned += (mem_total_failed[0] - mem_total_failed[1]) + (proc_total_failed[0] - proc_total_failed[1])
            pointsPossible = mem_total_failed[0] + proc_total_failed[0]
            pass
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

def doNothing(dut):
    pass

async def run_cycles(dut, n_cycles, each = doNothing):
    for i in range(n_cycles):
        print(f"cycle {i + 1}")
        await ClockCycles(dut.clk, 1)
        each(dut)
        print("")

def print_states(dut):
    print(f"F pc:{dut.datapath.f_pc_current.value.integer}, insn:{dut.datapath.f_insn.value.integer}, cycle:{dut.datapath.f_cycle_status.value.integer}")
    print(f"D pc:{dut.datapath.d_state_pc.value.integer}, insn:{dut.datapath.d_insn.value.integer}, cycle:{dut.datapath.d_state_cycle_status.value.integer}")
    print(f"X pc:{dut.datapath.x_state_pc.value.integer}, insn:{dut.datapath.x_state_insn.value.integer}, cycle:{dut.datapath.x_state_cycle_status.value.integer}, imm_u:{dut.datapath.x_state_imm_u_shifted.value.integer}")
    print(f"M pc:{dut.datapath.m_state_pc.value.integer}, insn:{dut.datapath.m_state_insn.value.integer}, cycle:{dut.datapath.m_state_cycle_status.value.integer}")
    print(f"W pc:{dut.datapath.w_state_pc.value.integer}, insn:{dut.datapath.w_state_insn.value.integer}, cycle:{dut.datapath.w_state_cycle_status.value.integer}")

def print_regfile(dut):
    print(f"rd: {dut.datapath.w_state_rd.value.integer}, rd_data: {dut.datapath.w_rd_data.value.integer}, rs1:{dut.datapath.x_state_rs1.value.integer}, rs2:{dut.datapath.x_state_rs2.value.integer}, we:{dut.datapath.w_state_reg_we.value.integer}")
    print(f"x1: {dut.datapath.rf.regs[1].value.integer}, x2: {dut.datapath.rf.regs[2].value.integer}, x3: {dut.datapath.rf.regs[3].value.integer}, x4: {dut.datapath.rf.regs[4].value.integer}")

def print_states_regfile(dut):
    print_states(dut)
    print_regfile(dut)

def print_regs(dut):
    print(f"x1: {dut.datapath.rf.regs[1].value.integer}, x2: {dut.datapath.rf.regs[2].value.integer}, x3: {dut.datapath.rf.regs[3].value.integer}, x4: {dut.datapath.rf.regs[4].value.integer}")

@cocotb.test()
async def testLui(dut):
    "Run one lui insn"
    asm(dut, 'lui x1,0x12345')
    await preTestSetup(dut)
    def p_w_rddata(dut):
        print(f"w_rd_data:{dut.datapath.m_state_rd_data.value.integer}, we:{dut.datapath.m_state_reg_we.value.integer}")
        print_regs(dut)
    # await run_cycles(dut, 6, print_states_regfile)
    await ClockCycles(dut.clk, 6)
    assert dut.datapath.rf.regs[1].value == 0x12345000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'

@cocotb.test()
async def testLuiLui(dut):
    "Run two lui independent insns"
    asm(dut, '''lui x1,0x12345
        lui x2,0x6789A''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 7)
    assert dut.datapath.rf.regs[1].value == 0x12345000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    assert dut.datapath.rf.regs[2].value == 0x6789A000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'

@cocotb.test()
async def testLui3(dut):
    "Run three lui independent insns"
    asm(dut, '''lui x1,0x12345
        lui x2,0x6789A
        lui x3,0xBCDEF''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 8)
    assert dut.datapath.rf.regs[1].value == 0x12345000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    assert dut.datapath.rf.regs[2].value == 0x6789A000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    assert dut.datapath.rf.regs[3].value == 0xBCDEF000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'

@cocotb.test()
async def testAddi3(dut):
    "Run three addi insns"
    asm(dut, '''addi x1,x1,1
        addi x1,x1,1
        addi x1,x1,1''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 8)
    assert dut.datapath.rf.regs[1].value == 3, f'failed at cycle {dut.datapath.cycles_current.value.integer}'

@cocotb.test()
async def testBneTaken(dut):
    "bne which is taken"
    asm(dut, '''
        lui x1,0x12345
        bne x1,x0,target
        lui x1,0x54321 # in Decode when branch is taken, should get cleared
        lui x1,0xABCDE # in Fetch when branch is taken, should get cleared
        target: addi x0,x0,0
        addi x0,x0,0
        ''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 9)
    assert dut.datapath.rf.regs[1].value == 0x12345000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    pass

@cocotb.test()
async def testBeqTaken(dut):
    "beq which is taken"
    asm(dut, '''
        lui x1,0x12345
        beq x1,x1,target
        lui x1,0x54321 # in Decode when branch is taken, should get cleared
        lui x1,0xABCDE # in Fetch when branch is taken, should get cleared
        target: addi x0,x0,0
        addi x0,x0,0
        ''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 9)
    assert dut.datapath.rf.regs[1].value == 0x12345000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    pass

@cocotb.test()
async def testTraceRvLui(dut):
    "Use the LUI riscv-test with trace comparison"
    await riscvTest(dut, RISCV_TESTS_PATH / 'rv32ui-p-lui', TRACING_MODE)

@cocotb.test()
async def testTraceRvBeq(dut):
    "Use the BEQ riscv-test with trace comparison"
    await riscvTest(dut, RISCV_TESTS_PATH / 'rv32ui-p-beq', TRACING_MODE)

#########################
## FULL ISA TEST CASES ##
#########################

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def testLoadUse1(dut):
    "load to use in rs1"
    asm(dut, '''
        lw x1,0(x0) # loads bits of the lw insn itself
        add x2,x1,x0
        ''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 8)
    assert dut.datapath.rf.regs[2].value == 0x0000_2083, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    pass

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def testLoadUse2(dut):
    "load to use in rs1"
    asm(dut, '''
        lw x1,0(x0) # loads bits of the lw insn itself
        add x2,x0,x1
        ''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 8)
    assert dut.datapath.rf.regs[2].value == 0x0000_2083, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    pass

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def testLoadFalseUse(dut):
    "load followed by insn that doesn't actually use load result"
    asm(dut, '''
        lw x0,0(x0) # loads bits of the lw insn itself
        lui x1,0xFE007
        ''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 7)
    assert dut.datapath.rf.regs[1].value == 0xFE00_7000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    pass

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def testWMData(dut):
    "WM bypass"
    asm(dut, '''
        lw x1,0(x0) # loads bits of the lw insn itself
        sw x1,12(x0)
        ''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 7)
    assert dut.mem.mem_array[3].value == 0x0000_2083, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    pass

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def testWMAddress(dut):
    "WM bypass"
    asm(dut, '''
        lw x1,0(x0) # loads bits of the lw insn itself
        sb x1,0(x1) # use sb since x1 is not 2B or 4B aligned
        ''')
    await preTestSetup(dut)
    loadValue = 0x2083

    await ClockCycles(dut.clk, 5) # sb in X stage
    assert dut.mem.mem_array[int(loadValue / 4)].value == 0, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    await ClockCycles(dut.clk, 2) # sb reaches W stage, memory write complete
    assert dut.mem.mem_array[int(loadValue / 4)].value == 0x8300_0000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    pass

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def testFence(dut):
    "Test fence insn"
    asm(dut, '''
        li x2,0xfffff0b7 # machine code for `lui x1,0xfffff`. NB: li needs 2 insn lui+addi sequence
        # addi part of li goes here
        sw x2,16(x0) # overwrite lui below
        fence # should stall until sw reaches Writeback
        lui x1,0x12345
        ''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 12)
    assert dut.datapath.rf.regs[1].value == 0xFFFF_F000, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    pass

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def testDiv(dut):
    "Run div insn"
    asm(dut, '''
        addi x1,x0,10
        addi x2,x0,2
        addi x5,x0,5
        div x3,x1,x2''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 9)
    assert dut.datapath.rf.regs[3].value == dut.datapath.rf.regs[5].value, f'failed at cycle {dut.datapath.cycles_current.value.integer}'

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def testDivUse(dut):
    "Run div + dependent insn"
    asm(dut, '''
        lui x1,0x12345
        div x2,x1,x1
        add x3,x2,x2 # needs stall + WX bypass
        ''')
    await preTestSetup(dut)

    await ClockCycles(dut.clk, 9)
    assert dut.datapath.rf.regs[2].value == 1, f'failed at cycle {dut.datapath.cycles_current.value.integer}'
    assert dut.datapath.rf.regs[3].value == 2, f'failed at cycle {dut.datapath.cycles_current.value.integer}'

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def testTraceRvLw(dut):
    "Use the LW riscv-test with trace comparison"
    await riscvTest(dut, RISCV_TESTS_PATH / 'rv32ui-p-lw', TRACING_MODE)

def handleTrace(dut, trace, traceIdx, tracingMode):
    if tracingMode == 'generate':
        traceElem = {}
        traceElem['cycle'] = dut.datapath.cycles_current.value.integer
        traceElem['trace_writeback_pc'] = f'0x{dut.datapath.trace_writeback_pc.value.integer:x}'
        traceElem['trace_writeback_insn'] = f'0x{dut.datapath.trace_writeback_insn.value.integer:08x}'
        traceElem['trace_writeback_cycle_status'] = dut.datapath.trace_writeback_cycle_status.value.integer
        trace.append(traceElem)
        pass
    elif tracingMode == 'compare':
        traceElem = trace[traceIdx]
        msg = f'trace validation error at cycle {traceElem["cycle"]}'
        assert int(traceElem['trace_writeback_pc'],16) == dut.datapath.trace_writeback_pc.value.integer, msg
        assert int(traceElem['trace_writeback_insn'],16) == dut.datapath.trace_writeback_insn.value.integer, msg
        assert traceElem['trace_writeback_cycle_status'] == dut.datapath.trace_writeback_cycle_status.value.integer, msg
        pass
    return

# tracingMode argument is one of `generate`, `compare` or None
async def riscvTest(dut, binaryPath=None, tracingMode=None):
    "Run the official RISC-V test whose binary lives at `binaryPath`"
    assert binaryPath is not None
    assert binaryPath.exists(), f'Could not find RV test binary {binaryPath}, have you built riscv-tests?'
    loadBinaryIntoMemory(dut, binaryPath)
    await preTestSetup(dut)

    trace = []
    if tracingMode == 'compare':
        # use ../ since we run from the sim_build directory
        with open(f'../trace-{binaryPath.name}.json', 'r', encoding='utf-8') as f:
            trace = json.load(f)
            pass
        pass

    dut._log.info(f'Running RISC-V test at {binaryPath} with tracingMode == {tracingMode}')
    for cycles in range(TIMEOUT_CYCLES):
        await RisingEdge(dut.clk)

        handleTrace(dut, trace, cycles, tracingMode)
        if dut.halt.value == 1:
            # see RVTEST_PASS and RVTEST_FAIL macros in riscv-tests/env/p/riscv_test.h
            assert 93 == dut.datapath.rf.regs[17].value.integer # magic value from pass/fail functions
            resultCode = dut.datapath.rf.regs[10].value.integer
            assert 0 == resultCode, f'failed test {resultCode >> 1} at cycle {dut.datapath.cycles_current.value.integer}'
            if tracingMode == 'generate':
                with open(f'trace-{binaryPath.name}.json', 'w', encoding='utf-8') as f:
                    json.dump(trace, f, indent=2)
                    pass
            return
        pass
    raise SimTimeoutError()

RV_TEST_BINARIES = [
    RISCV_TESTS_PATH / 'rv32ui-p-simple', # 1
    RISCV_TESTS_PATH / 'rv32ui-p-lui',
    
    RISCV_TESTS_PATH / 'rv32ui-p-and', # 3
    RISCV_TESTS_PATH / 'rv32ui-p-or',
    RISCV_TESTS_PATH / 'rv32ui-p-xor',
    RISCV_TESTS_PATH / 'rv32ui-p-sll',
    RISCV_TESTS_PATH / 'rv32ui-p-sra',
    RISCV_TESTS_PATH / 'rv32ui-p-srl',
    RISCV_TESTS_PATH / 'rv32ui-p-slt',
    RISCV_TESTS_PATH / 'rv32ui-p-add',
    RISCV_TESTS_PATH / 'rv32ui-p-sub',
    
    RISCV_TESTS_PATH / 'rv32ui-p-andi', # 12
    RISCV_TESTS_PATH / 'rv32ui-p-ori',
    RISCV_TESTS_PATH / 'rv32ui-p-slli',
    RISCV_TESTS_PATH / 'rv32ui-p-srai',
    RISCV_TESTS_PATH / 'rv32ui-p-srli',
    RISCV_TESTS_PATH / 'rv32ui-p-xori',
    RISCV_TESTS_PATH / 'rv32ui-p-slti',
    RISCV_TESTS_PATH / 'rv32ui-p-sltiu',
    RISCV_TESTS_PATH / 'rv32ui-p-sltu',
    RISCV_TESTS_PATH / 'rv32ui-p-addi',
    
    RISCV_TESTS_PATH / 'rv32ui-p-beq', # 22
    RISCV_TESTS_PATH / 'rv32ui-p-bge',
    RISCV_TESTS_PATH / 'rv32ui-p-bgeu',
    RISCV_TESTS_PATH / 'rv32ui-p-blt',
    RISCV_TESTS_PATH / 'rv32ui-p-bltu',
    RISCV_TESTS_PATH / 'rv32ui-p-bne',

    RISCV_TESTS_PATH / 'rv32ui-p-jal', # 28
    RISCV_TESTS_PATH / 'rv32ui-p-jalr',
    RISCV_TESTS_PATH / 'rv32ui-p-auipc', # needs JAL

    RISCV_TESTS_PATH / 'rv32ui-p-lw', # 31
    RISCV_TESTS_PATH / 'rv32ui-p-lh',
    RISCV_TESTS_PATH / 'rv32ui-p-lhu',
    RISCV_TESTS_PATH / 'rv32ui-p-lb',
    RISCV_TESTS_PATH / 'rv32ui-p-lbu',
    
    RISCV_TESTS_PATH / 'rv32ui-p-sw', # 36
    RISCV_TESTS_PATH / 'rv32ui-p-sh',
    RISCV_TESTS_PATH / 'rv32ui-p-sb',

    # self-modifying code and fence.i insn
    RISCV_TESTS_PATH / 'rv32ui-p-fence_i', # 39

    RISCV_TESTS_PATH / 'rv32um-p-mul', # 40
    RISCV_TESTS_PATH / 'rv32um-p-mulh',
    RISCV_TESTS_PATH / 'rv32um-p-mulhsu',
    RISCV_TESTS_PATH / 'rv32um-p-mulhu',
    RISCV_TESTS_PATH / 'rv32um-p-div', # 44
    RISCV_TESTS_PATH / 'rv32um-p-divu',
    RISCV_TESTS_PATH / 'rv32um-p-rem',
    RISCV_TESTS_PATH / 'rv32um-p-remu',

    # misaligned accesses, we don't support these
    #RISCV_TESTS_PATH / 'rv32ui-p-ma_data',
]

rvTestFactory = TestFactory(test_function=riscvTest)
if 'RVTEST_ALUBR' in os.environ:
    RV_TEST_BINARIES = RV_TEST_BINARIES[:27]
    pass
rvTestFactory.add_option(name='binaryPath', optionlist=RV_TEST_BINARIES)
rvTestFactory.generate_tests()

@cocotb.test(skip='RVTEST_ALUBR' in os.environ)
async def dhrystone(dut, tracingMode=TRACING_MODE):
    "Run dhrystone benchmark from riscv-tests"
    dsBinary = RISCV_BENCHMARKS_PATH / 'dhrystone.riscv' 
    assert dsBinary.exists(), f'Could not find Dhrystone binary {dsBinary}, have you built riscv-tests?'
    loadBinaryIntoMemory(dut, dsBinary)
    await preTestSetup(dut)

    trace = []
    if tracingMode == 'compare':
        # use ../ since we run from the sim_build directory
        with open(f'../trace-{dsBinary.name}.json', 'r', encoding='utf-8') as f:
            trace = json.load(f)
            pass
        pass

    dut._log.info(f'Running Dhrystone benchmark (takes 255k cycles)... with tracingMode == {tracingMode}')
    for cycles in range(280_000):
        await RisingEdge(dut.clk)

        handleTrace(dut, trace, cycles, tracingMode)
        if cycles > 0 and 0 == cycles % 10_000:
            dut._log.info(f'ran {int(cycles/1000)}k cycles...')
            pass
        if dut.halt.value == 1:
            # there are 22 output checks, each sets 1 bit
            expectedValue = (1<<22) - 1
            assert expectedValue == dut.datapath.rf.regs[5].value.integer
            latency_millis = (cycles / 15_000_000) * 1000
            dut._log.info(f'dhrystone passed after {cycles} cycles, {latency_millis} milliseconds with 15MHz clock')
            
            if tracingMode == 'generate':
                with open(f'trace-{dsBinary.name}.json', 'w', encoding='utf-8') as f:
                    json.dump(trace, f, indent=2)
                    pass
            
            return
        pass
    raise SimTimeoutError()