`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // Reads
  assign rs1_data = regs[rs1];  // read from rs1
  assign rs2_data = regs[rs2];  // read from rs2
  assign regs[0]  = 32'd0;  // x0 is hardwired to 0

  // Writes
  // what does always_ff do? It's a clocked always block, meaning it only runs when the clock is 1
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 1; i < NumRegs; i++) begin
        regs[i] <= 32'd0;  // Reset all registers to 0, except for reg[0]
      end
    end else if (we && rd != 5'd0) begin
      regs[rd] <= rd_data;
    end
  end

endmodule

/** NB: ARESETn is active-low, i.e., reset when this input is ZERO */
interface axi_clkrst_if (
    input wire ACLK,
    input wire ARESETn
);
endinterface

interface axi_if #(
      parameter int ADDR_WIDTH = 32
    , parameter int DATA_WIDTH = 32
);
  logic                      ARVALID;
  logic                      ARREADY;
  logic [    ADDR_WIDTH-1:0] ARADDR;
  logic [               2:0] ARPROT;

  logic                      RVALID;
  logic                      RREADY;
  logic [    DATA_WIDTH-1:0] RDATA;
  logic [               1:0] RRESP;

  logic                      AWVALID;
  logic                      AWREADY;
  logic [    ADDR_WIDTH-1:0] AWADDR;
  logic [               2:0] AWPROT;

  logic                      WVALID;
  logic                      WREADY;
  logic [    DATA_WIDTH-1:0] WDATA;
  logic [(DATA_WIDTH/8)-1:0] WSTRB;

  logic                      BVALID;
  logic                      BREADY;
  logic [               1:0] BRESP;

  modport manager(
      input ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP,
      output ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY
  );
  modport subord(
      input ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY,
      output ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP
  );
endinterface

module MemoryAxiLite #(
    parameter int NUM_WORDS  = 32,
    // parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    axi_clkrst_if axi,
    axi_if.subord insn,
    axi_if.subord data
);

  // memory is an array of 4B words
  logic [DATA_WIDTH-1:0] mem_array[NUM_WORDS];
  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  // [BR]RESP codes, from Section A 3.4.4 of AXI4 spec
  localparam bit [1:0] ResponseOkay = 2'b00;
  // localparam bit [1:0] ResponseSubordinateError = 2'b10;
  // localparam bit [1:0] ResponseDecodeError = 2'b11;

`ifndef FORMAL
  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (!insn.ARVALID || insn.ARADDR[1:0] == 2'b00);
    assert (!data.ARVALID || data.ARADDR[1:0] == 2'b00);
    assert (!data.AWVALID || data.AWADDR[1:0] == 2'b00);
    // we don't use the protection bits
    assert (insn.ARPROT == 3'd0);
    assert (data.ARPROT == 3'd0);
    assert (data.AWPROT == 3'd0);
  end
`endif

  always_ff @(posedge axi.ACLK) begin
    if (!axi.ARESETn) begin
      // start out ready to accept incoming reads
      insn.ARREADY <= 1;
      data.ARREADY <= 1;
      // start out ready to accept an incoming write
      data.AWREADY <= 1;
      data.WREADY  <= 1;
      insn.RDATA   <= 0;
      data.RDATA   <= 0;
    end else begin
      if (insn.ARREADY == 1 && insn.ARVALID == 1) begin
        insn.RVALID <= 1;
        insn.RRESP  <= ResponseOkay;
        insn.RDATA  <= mem_array[insn.ARADDR[AddrMsb:AddrLsb]];
      end else insn.RVALID <= 0;
      if (data.ARREADY == 1 && data.ARVALID == 1) begin
        data.RVALID <= 1;
        data.RRESP  <= ResponseOkay;
        data.RDATA  <= mem_array[data.ARADDR[AddrMsb:AddrLsb]];
      end else data.RVALID <= 0;
      if (data.AWVALID && data.AWREADY && data.WVALID && data.WREADY && data.BREADY) begin
        data.BVALID <= 1;
        data.BRESP  <= ResponseOkay;
        if (data.WSTRB[0]) mem_array[data.AWADDR[AddrMsb:AddrLsb]][7:0] <= data.WDATA[7:0];
        if (data.WSTRB[1]) mem_array[data.AWADDR[AddrMsb:AddrLsb]][15:8] <= data.WDATA[15:8];
        if (data.WSTRB[2]) mem_array[data.AWADDR[AddrMsb:AddrLsb]][23:16] <= data.WDATA[23:16];
        if (data.WSTRB[3]) mem_array[data.AWADDR[AddrMsb:AddrLsb]][31:24] <= data.WDATA[31:24];
      end else insn.BVALID <= 0;
    end
  end

endmodule

/** This is used for testing MemoryAxiLite in simulation, since Verilator doesn't allow
SV interfaces in top-level modules. We expose all of the AXIL signals here so that tests
can interact with them. */
module MemAxiLiteTester #(
    parameter int NUM_WORDS  = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input wire ACLK,
    input wire ARESETn,

    input  wire                   I_ARVALID,
    output logic                  I_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] I_ARADDR,
    input  wire  [           2:0] I_ARPROT,
    output logic                  I_RVALID,
    input  wire                   I_RREADY,
    output logic [ADDR_WIDTH-1:0] I_RDATA,
    output logic [           1:0] I_RRESP,

    input  wire                       I_AWVALID,
    output logic                      I_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] I_AWADDR,
    input  wire  [               2:0] I_AWPROT,
    input  wire                       I_WVALID,
    output logic                      I_WREADY,
    input  wire  [    DATA_WIDTH-1:0] I_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] I_WSTRB,
    output logic                      I_BVALID,
    input  wire                       I_BREADY,
    output logic [               1:0] I_BRESP,

    input  wire                   D_ARVALID,
    output logic                  D_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] D_ARADDR,
    input  wire  [           2:0] D_ARPROT,
    output logic                  D_RVALID,
    input  wire                   D_RREADY,
    output logic [ADDR_WIDTH-1:0] D_RDATA,
    output logic [           1:0] D_RRESP,

    input  wire                       D_AWVALID,
    output logic                      D_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] D_AWADDR,
    input  wire  [               2:0] D_AWPROT,
    input  wire                       D_WVALID,
    output logic                      D_WREADY,
    input  wire  [    DATA_WIDTH-1:0] D_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] D_WSTRB,
    output logic                      D_BVALID,
    input  wire                       D_BREADY,
    output logic [               1:0] D_BRESP
);

  axi_clkrst_if axi (.*);
  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) insn ();
  assign insn.manager.ARVALID = I_ARVALID;
  assign I_ARREADY = insn.manager.ARREADY;
  assign insn.manager.ARADDR = I_ARADDR;
  assign insn.manager.ARPROT = I_ARPROT;
  assign I_RVALID = insn.manager.RVALID;
  assign insn.manager.RREADY = I_RREADY;
  assign I_RRESP = insn.manager.RRESP;
  assign I_RDATA = insn.manager.RDATA;

  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) data ();
  assign data.manager.ARVALID = D_ARVALID;
  assign D_ARREADY = data.manager.ARREADY;
  assign data.manager.ARADDR = D_ARADDR;
  assign data.manager.ARPROT = D_ARPROT;
  assign D_RVALID = data.manager.RVALID;
  assign data.manager.RREADY = D_RREADY;
  assign D_RRESP = data.manager.RRESP;
  assign D_RDATA = data.manager.RDATA;

  assign data.manager.AWVALID = D_AWVALID;
  assign D_AWREADY = data.manager.AWREADY;
  assign data.manager.AWADDR = D_AWADDR;
  assign data.manager.AWPROT = D_AWPROT;
  assign data.manager.WVALID = D_WVALID;
  assign D_WREADY = data.manager.WREADY;
  assign data.manager.WDATA = D_WDATA;
  assign data.manager.WSTRB = D_WSTRB;
  assign D_BVALID = data.manager.BVALID;
  assign data.manager.BREADY = D_BREADY;
  assign D_BRESP = data.manager.BRESP;

  MemoryAxiLite #(
      .NUM_WORDS(NUM_WORDS)
  ) mem (
      .axi (axi),
      .insn(insn.subord),
      .data(data.subord)
  );
endmodule

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,
  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence insn */
  CYCLE_FENCE = 32
} cycle_status_e;

/* not using packed structs anymore because i can't print their fields in cocotb */

typedef enum {
  INSN_NOP = 0,
  INSN_LUI, INSN_AUIPC,
  INSN_ADDI, INSN_SLTI, INSN_SLTIU, INSN_XORI, INSN_ORI, INSN_ANDI, INSN_SLLI, INSN_SRLI, INSN_SRAI,
  INSN_ADD, INSN_SUB, INSN_SLL, INSN_SLT, INSN_SLTU, INSN_XOR, INSN_SRL, INSN_SRA, INSN_OR, INSN_AND,
  INSN_LB, INSN_LH, INSN_LW, INSN_LBU, INSN_LHU,
  INSN_SB, INSN_SH, INSN_SW,
  INSN_JAL, INSN_JALR,
  INSN_BEQ, INSN_BNE, INSN_BLT, INSN_BGE, INSN_BLTU, INSN_BGEU,
  INSN_ECALL,
  INSN_FENCE,
  INSN_MUL, INSN_MULH, INSN_MULHSU, INSN_MULHU,
  INSN_DIV, INSN_DIVU, INSN_REM, INSN_REMU,
  INSN_INVALID
} insn_type_t;

typedef enum {
  RD_NORMAL,
  RD_QUOTIENT,
  RD_MINUS_QUOTIENT,
  RD_REMAINDER,
  RD_MINUS_REMAINDER
} rd_type_t;

module decode_insn(input logic [`INSN_SIZE] insn,
  output insn_type_t insn_type,
  output logic [4:0] rs1,
  output logic [4:0] rs2,
  output logic [4:0] rd,
  output logic [31:0] imm_u_shifted,
  output logic [31:0] imm_i_sext,
  output logic [31:0] imm_b_sext,
  output logic [31:0] imm_j_sext,
  output logic [31:0] imm_s_sext
  );

  wire [6:0] fun7;
  wire [2:0] fun3;
  wire [`OPCODE_SIZE] opcode;
  assign {fun7, rs2, rs1, fun3, rd, opcode} = insn;

  assign imm_u_shifted = {insn[31:12], 12'b0};
  assign imm_i_sext = {{20{insn[31]}}, insn[31:20]};

  wire [12:1] imm_b;
  assign {imm_b[12], imm_b[10:5]} = fun7;
  assign {imm_b[4:1], imm_b[11]} = rd;
  assign imm_b_sext = {{19{imm_b[12]}}, imm_b[12:1], 1'b0};

  wire [20:1] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12]} = {fun7, rs2, rs1, fun3};
  assign imm_j_sext = {{11{imm_j[20]}}, imm_j[20:1], 1'b0};

  wire [11:0] imm_s;
  assign {imm_s[11:5], imm_s[4:0]} = {fun7, rd};
  assign imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};

  always_comb begin
    if (opcode == 0) insn_type = INSN_NOP;
    else if (opcode == 7'd55) insn_type = INSN_LUI;
    else if (opcode == 7'd23) insn_type = INSN_AUIPC;
    else if (opcode == 7'd19 && fun3 == 3'b000) insn_type = INSN_ADDI;
    else if (opcode == 7'd19 && fun3 == 3'b010) insn_type = INSN_SLTI;
    else if (opcode == 7'd19 && fun3 == 3'b011) insn_type = INSN_SLTIU;
    else if (opcode == 7'd19 && fun3 == 3'b100) insn_type = INSN_XORI;
    else if (opcode == 7'd19 && fun3 == 3'b110) insn_type = INSN_ORI;
    else if (opcode == 7'd19 && fun3 == 3'b111) insn_type = INSN_ANDI;
    else if (opcode == 7'd19 && fun3 == 3'b001 && fun7 == 7'h0) insn_type = INSN_SLLI;
    else if (opcode == 7'd19 && fun3 == 3'b101 && fun7 == 7'h0) insn_type = INSN_SRLI;
    else if (opcode == 7'd19 && fun3 == 3'b101 && fun7 == 7'h20) insn_type = INSN_SRAI;
    else if (opcode == 7'd51 && fun3 == 3'b000 && fun7 == 7'h0) insn_type = INSN_ADD;
    else if (opcode == 7'd51 && fun3 == 3'b000 && fun7 == 7'h20) insn_type = INSN_SUB;
    else if (opcode == 7'd51 && fun3 == 3'b001 && fun7 == 7'h0) insn_type = INSN_SLL;
    else if (opcode == 7'd51 && fun3 == 3'b010 && fun7 == 7'h0) insn_type = INSN_SLT;
    else if (opcode == 7'd51 && fun3 == 3'b011 && fun7 == 7'h0) insn_type = INSN_SLTU;
    else if (opcode == 7'd51 && fun3 == 3'b100 && fun7 == 7'h0) insn_type = INSN_XOR;
    else if (opcode == 7'd51 && fun3 == 3'b101 && fun7 == 7'h0) insn_type = INSN_SRL;
    else if (opcode == 7'd51 && fun3 == 3'b101 && fun7 == 7'h20) insn_type = INSN_SRA;
    else if (opcode == 7'd51 && fun3 == 3'b110 && fun7 == 7'h0) insn_type = INSN_OR;
    else if (opcode == 7'd51 && fun3 == 3'b111 && fun7 == 7'h0) insn_type = INSN_AND;
    else if (opcode == 7'd3 && fun3 == 3'b000) insn_type = INSN_LB;
    else if (opcode == 7'd3 && fun3 == 3'b001) insn_type = INSN_LH;
    else if (opcode == 7'd3 && fun3 == 3'b010) insn_type = INSN_LW;
    else if (opcode == 7'd3 && fun3 == 3'b100) insn_type = INSN_LBU;
    else if (opcode == 7'd3 && fun3 == 3'b101) insn_type = INSN_LHU;
    else if (opcode == 7'd35 && fun3 == 3'b000) insn_type = INSN_SB;
    else if (opcode == 7'd35 && fun3 == 3'b001) insn_type = INSN_SH;
    else if (opcode == 7'd35 && fun3 == 3'b010) insn_type = INSN_SW;
    else if (opcode == 7'd111) insn_type = INSN_JAL;
    else if (opcode == 7'd103 && fun3 == 3'b000) insn_type = INSN_JALR;
    else if (opcode == 7'd99 && fun3 == 3'b000) insn_type = INSN_BEQ;
    else if (opcode == 7'd99 && fun3 == 3'b001) insn_type = INSN_BNE;
    else if (opcode == 7'd99 && fun3 == 3'b100) insn_type = INSN_BLT;
    else if (opcode == 7'd99 && fun3 == 3'b101) insn_type = INSN_BGE;
    else if (opcode == 7'd99 && fun3 == 3'b110) insn_type = INSN_BLTU;
    else if (opcode == 7'd99 && fun3 == 3'b111) insn_type = INSN_BGEU;
    else if (opcode == 7'd115 && insn[31:7] == 0) insn_type = INSN_ECALL;
    else if (opcode == 7'd15) insn_type = INSN_FENCE;
    else if (opcode == 7'd51 && fun3 == 3'b000 && fun7 == 7'h1) insn_type = INSN_MUL;
    else if (opcode == 7'd51 && fun3 == 3'b001 && fun7 == 7'h1) insn_type = INSN_MULH;
    else if (opcode == 7'd51 && fun3 == 3'b010 && fun7 == 7'h1) insn_type = INSN_MULHSU;
    else if (opcode == 7'd51 && fun3 == 3'b011 && fun7 == 7'h1) insn_type = INSN_MULHU;
    else if (opcode == 7'd51 && fun3 == 3'b100 && fun7 == 7'h1) insn_type = INSN_DIV;
    else if (opcode == 7'd51 && fun3 == 3'b101 && fun7 == 7'h1) insn_type = INSN_DIVU;
    else if (opcode == 7'd51 && fun3 == 3'b110 && fun7 == 7'h1) insn_type = INSN_REM;
    else if (opcode == 7'd51 && fun3 == 3'b111 && fun7 == 7'h1) insn_type = INSN_REMU;
    else insn_type = INSN_INVALID;
  end

endmodule

module DatapathAxilMemory (
    input wire clk,
    input wire rst,

    // Start by replacing this interface to imem...
    // output logic [`REG_SIZE] pc_to_imem,
    // input wire [`INSN_SIZE] insn_from_imem,
    // ...with this AXIL one.
    axi_if.manager imem,

    // Once imem is working, replace this interface to dmem...
    // output logic [`REG_SIZE] addr_to_dmem,
    // input wire [`REG_SIZE] load_data_from_dmem,
    // output logic [`REG_SIZE] store_data_to_dmem,
    // output logic [3:0] store_we_to_dmem,
    // ...with this AXIL one
    axi_if.manager dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);
  // no longer using structs because i can't get their fields in cocotb
  // decode state
  logic [31:0]   d_state_pc;
  logic [31:0]   d_state_insn;
  cycle_status_e d_state_cycle_status;
  // execute state
  logic [31:0]   x_state_pc;
  logic [31:0]   x_state_insn;
  cycle_status_e x_state_cycle_status;
  logic [4:0]    x_state_rs1;
  logic [4:0]    x_state_rs2;
  logic [4:0]    x_state_rd;
  logic [31:0]   x_state_imm_u_shifted;
  logic [31:0]   x_state_imm_i_sext;
  logic [31:0]   x_state_imm_b_sext;
  logic [31:0]   x_state_imm_s_sext;
  logic [31:0]   x_state_imm_j_sext;
  insn_type_t    x_state_insn_type;
  // memory state
  logic [31:0]   m_state_pc;
  logic [31:0]   m_state_insn;
  cycle_status_e m_state_cycle_status;
  logic [4:0]    m_state_rd;
  logic [4:0]    m_state_rs2;
  logic [31:0]   m_state_rd_data;
  rd_type_t      m_state_rd_type;
  logic [31:0]   m_state_rs2_data;
  logic [31:0]   m_state_addr_to_dmem;
  insn_type_t    m_state_insn_type;
  logic          m_state_reg_we;
  logic          m_state_halt;
  // writeback state
  logic [31:0]   w_state_pc;
  logic [31:0]   w_state_insn;
  cycle_status_e w_state_cycle_status;
  insn_type_t    w_state_insn_type;
  logic [4:0]    w_state_rd;
  logic [31:0]   w_state_rd_data;
  logic [31:0]   w_state_addr_to_dmem;
  logic          w_state_reg_we;
  logic          w_state_halt;
  
  // stall flags
  logic branch_stalling, load_stalling, div_stalling, fence_stalling;
  logic [31:0] branching_to;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  // DON'T TOUCH THIS
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  logic [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;
  
  assign f_insn = imem.RDATA;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current   <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (branch_stalling) begin
      f_pc_current   <= branching_to;
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (load_stalling || div_stalling || fence_stalling) begin
      f_pc_current   <= f_pc_current;
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_pc_current   <= f_pc_current + 4;
      f_cycle_status <= CYCLE_NO_STALL;
    end
  end

  assign imem.ARVALID = 1;
  assign imem.RREADY  = 1;
  assign imem.ARADDR  = f_pc_current;
  
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/
  // storing the old insn because i couldn't get it to work the same as hw5
  // not sure what the axil memory broke here but it was a cycle behind using the original way
  logic d_keep_old;
  always_ff @(posedge clk) begin
    if (rst) begin
      d_keep_old <= 0;
      d_state_pc <= 0;
      d_state_cycle_status <= CYCLE_RESET;
    end else if (branch_stalling) begin
      d_keep_old <= 0;
      d_state_pc <= 0;
      d_state_cycle_status <= CYCLE_TAKEN_BRANCH;
    end else if (load_stalling || div_stalling || fence_stalling) begin
      d_keep_old <= 1;
      d_state_pc <= d_state_pc;
      d_state_cycle_status <= CYCLE_NO_STALL;
    end else begin
      d_keep_old <= 0;
      d_state_pc <= f_pc_current;
      d_state_cycle_status <= f_cycle_status;
    end
  end
  
  logic [31:0] d_old;
  always_ff @(posedge clk) begin
    if (d_keep_old) d_old <= d_old;
    else d_old <= d_state_insn;
  end
  
  always_comb begin
    d_state_insn = f_insn;
    if (d_state_cycle_status == CYCLE_TAKEN_BRANCH) d_state_insn = 0;
    if (d_keep_old) d_state_insn = d_old;
  end
    
  
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_decode (
      .insn  (d_state_insn),
      .disasm(d_disasm)
  );

  wire [4:0] d_rs1; wire [4:0] d_rs2; wire [4:0] d_rd;
  insn_type_t d_insn_type;
  wire [31:0] d_imm_u_shifted; wire [31:0] d_imm_i_sext; wire [31:0] d_imm_b_sext;
  wire [31:0] d_imm_j_sext; wire [31:0] d_imm_s_sext;
  decode_insn d_state_decode(.insn(d_state_insn),
    .insn_type(d_insn_type),
    .rs1(d_rs1), .rs2(d_rs2), .rd(d_rd),
    .imm_u_shifted(d_imm_u_shifted), .imm_i_sext(d_imm_i_sext), .imm_b_sext(d_imm_b_sext),
    .imm_j_sext(d_imm_j_sext), .imm_s_sext(d_imm_s_sext)
  );
  
  logic d_uses_rs1, d_uses_rs2, d_is_store, x_is_load, x_is_div, x_is_store, m_is_store;
  always_comb begin
    d_uses_rs1 = d_insn_type != INSN_LUI && d_insn_type != INSN_AUIPC &&
      d_insn_type != INSN_JAL && d_insn_type != INSN_ECALL &&
      d_insn_type != INSN_FENCE;
    d_uses_rs2 = d_uses_rs1 && d_insn_type != INSN_ADDI && d_insn_type != INSN_SLTI &&
      d_insn_type != INSN_SLTIU && d_insn_type != INSN_XORI &&
      d_insn_type != INSN_ORI && d_insn_type != INSN_ANDI &&
      d_insn_type != INSN_SLLI && d_insn_type != INSN_SRLI &&
      d_insn_type != INSN_SRAI && d_insn_type != INSN_LB &&
      d_insn_type != INSN_LH && d_insn_type != INSN_LW && d_insn_type != INSN_LBU &&
      d_insn_type != INSN_LHU && d_insn_type != INSN_JALR;
    d_is_store = d_insn_type == INSN_SB || d_insn_type == INSN_SH || d_insn_type == INSN_SW;
    x_is_load = x_state_insn_type == INSN_LB || x_state_insn_type == INSN_LH ||
      x_state_insn_type == INSN_LW || x_state_insn_type == INSN_LBU ||
      x_state_insn_type == INSN_LHU;
    x_is_div = x_state_insn_type == INSN_DIV || x_state_insn_type == INSN_DIVU ||
      x_state_insn_type == INSN_REM || x_state_insn_type == INSN_REMU;
    x_is_store = x_state_insn_type == INSN_SB ||
      x_state_insn_type == INSN_SH || x_state_insn_type == INSN_SW;
    m_is_store = m_state_insn_type == INSN_SB ||
      m_state_insn_type == INSN_SH || m_state_insn_type == INSN_SW;
    load_stalling =
      (x_is_load && x_state_rd == d_rs1 && d_rs1 != 0 && d_uses_rs1) ||
      (x_is_load && x_state_rd == d_rs2 && d_rs2 != 0 && d_uses_rs2 && ~d_is_store);
    div_stalling =
      (x_is_div && x_state_rd == d_rs1 && d_rs1 != 0 && d_uses_rs1) ||
      (x_is_div && x_state_rd == d_rs2 && d_rs2 != 0 && d_uses_rs2);
    fence_stalling =  d_insn_type == INSN_FENCE && (x_is_store || m_is_store);
  end

  /*****************/
  /* EXECUTE STAGE */
  /*****************/
  always_ff @(posedge clk) begin
    if (rst) begin
      x_state_pc <= 0;
      x_state_insn <= 0;
      x_state_cycle_status <= CYCLE_RESET;
      x_state_rs1 <= 0;
      x_state_rs2 <= 0;
      x_state_rd <= 0;
      x_state_imm_u_shifted <= 0;
      x_state_imm_i_sext <= 0;
      x_state_imm_b_sext <= 0;
      x_state_imm_s_sext <= 0;
      x_state_imm_j_sext <= 0;
      x_state_insn_type <= INSN_NOP;
    end else if (load_stalling) begin
      x_state_pc <= 0;
      x_state_insn <= 0;
      x_state_cycle_status <= CYCLE_LOAD2USE;
      x_state_rs1 <= 0;
      x_state_rs2 <= 0;
      x_state_rd <= 0;
      x_state_imm_u_shifted <= 0;
      x_state_imm_i_sext <= 0;
      x_state_imm_b_sext <= 0;
      x_state_imm_s_sext <= 0;
      x_state_imm_j_sext <= 0;
      x_state_insn_type <= INSN_NOP;
    end else if (div_stalling) begin
      x_state_pc <= 0;
      x_state_insn <= 0;
      x_state_cycle_status <= CYCLE_DIV2USE;
      x_state_rs1 <= 0;
      x_state_rs2 <= 0;
      x_state_rd <= 0;
      x_state_imm_u_shifted <= 0;
      x_state_imm_i_sext <= 0;
      x_state_imm_b_sext <= 0;
      x_state_imm_s_sext <= 0;
      x_state_imm_j_sext <= 0;
      x_state_insn_type <= INSN_NOP;
    end else if (branch_stalling) begin
      x_state_pc <= 0;
      x_state_insn <= 0;
      x_state_cycle_status <= CYCLE_TAKEN_BRANCH;
      x_state_rs1 <= 0;
      x_state_rs2 <= 0;
      x_state_rd <= 0;
      x_state_imm_u_shifted <= 0;
      x_state_imm_i_sext <= 0;
      x_state_imm_b_sext <= 0;
      x_state_imm_s_sext <= 0;
      x_state_imm_j_sext <= 0;
      x_state_insn_type <= INSN_NOP;
    end else begin
      x_state_pc <= d_state_pc;
      x_state_insn <= d_state_insn;
      x_state_cycle_status <= d_state_cycle_status;
      x_state_rs1 <= d_rs1;
      x_state_rs2 <= d_rs2;
      x_state_rd <= d_rd;
      x_state_imm_u_shifted <= d_imm_u_shifted;
      x_state_imm_i_sext <= d_imm_i_sext;
      x_state_imm_b_sext <= d_imm_b_sext;
      x_state_imm_s_sext <= d_imm_s_sext;
      x_state_imm_j_sext <= d_imm_j_sext;
      x_state_insn_type <= d_insn_type;
    end
  end
  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_execute (
      .insn  (x_state_insn),
      .disasm(x_disasm)
  );

  // the testbench requires that your register file instance is named `rf`
  logic [31:0] x_rs1_rf;
  logic [31:0] x_rs2_rf;
  RegFile rf(
      .rd(w_state_rd), .rd_data(w_rd_data),
      .rs1(x_state_rs1), .rs1_data(x_rs1_rf),
      .rs2(x_state_rs2), .rs2_data(x_rs2_rf),
      .clk(clk), .we(w_state_reg_we), .rst(rst)
  );
  
  logic [31:0] x_rs1_data;
  logic [31:0] x_rs2_data;
  
  // MX and WX bypassing
  assign x_rs1_data = ((x_state_rs1 == m_state_rd) && (x_state_rs1 != 0)) ? m_state_rd_data : (
    ((x_state_rs1 == w_state_rd) && (x_state_rs1 != 0)) ? w_rd_data : x_rs1_rf
  );
  assign x_rs2_data = ((x_state_rs2 == m_state_rd) && (x_state_rs2 != 0)) ? m_state_rd_data : (
    ((x_state_rs2 == w_state_rd) && (x_state_rs2 != 0)) ? w_rd_data : x_rs2_rf
  );
  
  logic [31:0] x;
  logic [31:0] y;
  logic [31:0] sum;

  cla adder(.a(x), .b(y), .cin(0), .sum(sum));

  logic [31:0] quotient;
  logic [31:0] remainder;

  divider_unsigned_pipelined unsigned_div (
      .clk(clk), .rst(rst),
      .i_dividend(x), .i_divisor(y),
      .o_remainder(remainder), .o_quotient(quotient)
  );
  
  logic [63:0] product;
  logic [31:0] x_addr_to_dmem;
  logic x_reg_we;
  logic [4:0] x_rd;
  logic [31:0] x_rd_data;
  rd_type_t x_rd_type;
  logic x_halt;

  always_comb begin
  
    x_rd = 0;
    x_rd_data = 0;
    x_reg_we = 0;
    x = x_rs1_data;
    y = x_rs2_data;
    branch_stalling = 0;
    branching_to = 0;
    x_addr_to_dmem = 0;
    x_rd_type = RD_NORMAL;
    x_halt = 0;
    x_addr_to_dmem = 0;
    
    case (x_state_insn_type)

      INSN_LUI: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_state_imm_u_shifted;
      end

      INSN_AUIPC: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_state_pc + x_state_imm_u_shifted;
      end

      INSN_ADDI: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        y = x_state_imm_i_sext;
        x_rd_data = sum;
      end

      INSN_SLTI: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = $signed(x_rs1_data) < $signed(x_state_imm_i_sext) ? 1 : 0;
      end

      INSN_SLTIU: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data < x_state_imm_i_sext ? 1 : 0;
      end

      INSN_XORI: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data ^ x_state_imm_i_sext;
      end

      INSN_ORI: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data | x_state_imm_i_sext;
      end

      INSN_ANDI: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data & x_state_imm_i_sext;
      end

      INSN_SLLI: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data << x_state_imm_i_sext[4:0];
      end

      INSN_SRLI: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data >> x_state_imm_i_sext[4:0];
      end

      INSN_SRAI: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = $signed(x_rs1_data) >>> x_state_imm_i_sext[4:0];
      end

      INSN_ADD: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = sum;
      end

      INSN_SUB: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        y = ~x_rs2_data + 1;
        x_rd_data = sum;
      end

      INSN_SLL: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data << x_rs2_data[4:0];
      end

      INSN_SLT: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = $signed(x_rs1_data) < $signed(x_rs2_data) ? 1 : 0;
      end

      INSN_SLTU: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data < x_rs2_data ? 1 : 0;
      end

      INSN_XOR: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data ^ x_rs2_data;
      end

      INSN_SRL: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data >> x_rs2_data[4:0];
      end

      INSN_SRA: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = $signed(x_rs1_data) >>> x_rs2_data[4:0];
      end

      INSN_OR: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data | x_rs2_data;
      end

      INSN_AND: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data & x_rs2_data;
      end

      INSN_LB: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_addr_to_dmem = x_rs1_data + x_state_imm_i_sext;
      end

      INSN_LH: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_addr_to_dmem = x_rs1_data + x_state_imm_i_sext;
      end

      INSN_LW: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_addr_to_dmem = x_rs1_data + x_state_imm_i_sext;
      end

      INSN_LBU: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_addr_to_dmem = x_rs1_data + x_state_imm_i_sext;
      end

      INSN_LHU: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_addr_to_dmem = x_rs1_data + x_state_imm_i_sext;
      end

      INSN_SB: x_addr_to_dmem = x_rs1_data + x_state_imm_s_sext;
      INSN_SH: x_addr_to_dmem = x_rs1_data + x_state_imm_s_sext;
      INSN_SW: x_addr_to_dmem = x_rs1_data + x_state_imm_s_sext;

      INSN_JAL: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_state_pc + 4;
        branch_stalling = 1;
        branching_to = x_state_pc + x_state_imm_j_sext;
      end

      INSN_JALR: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_state_pc + 4;
        branch_stalling = 1;
        branching_to = (x_rs1_data + x_state_imm_i_sext) & ~32'b1;
      end
      
      INSN_BEQ: begin
        if (x_rs1_data == x_rs2_data) begin
          branch_stalling = 1;
          branching_to = x_state_pc + x_state_imm_b_sext;
        end
      end

      INSN_BNE: begin
        if (x_rs1_data != x_rs2_data) begin
          branch_stalling = 1;
          branching_to = x_state_pc + x_state_imm_b_sext;
        end
      end

      INSN_BLT: begin
        if ($signed(x_rs1_data) < $signed(x_rs2_data)) begin
          branch_stalling = 1;
          branching_to = x_state_pc + x_state_imm_b_sext;
        end
      end

      INSN_BGE: begin
        if ($signed(x_rs1_data) >= $signed(x_rs2_data)) begin
          branch_stalling = 1;
          branching_to = x_state_pc + x_state_imm_b_sext;
        end
      end

      INSN_BLTU: begin
        if (x_rs1_data < x_rs2_data) begin
          branch_stalling = 1;
          branching_to = x_state_pc + x_state_imm_b_sext;
        end
      end

      INSN_BGEU: begin
        if (x_rs1_data >= x_rs2_data) begin
          branch_stalling = 1;
          branching_to = x_state_pc + x_state_imm_b_sext;
        end
      end

      INSN_ECALL: begin
        x_halt = 1;
      end

      INSN_FENCE: begin
        // do nothing in execute stage for fence?
      end

      INSN_MUL: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_data = x_rs1_data * x_rs2_data;
      end

      INSN_MULH: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        product = { {32{x_rs1_data[31]}}, x_rs1_data} * { {32{x_rs2_data[31]}}, x_rs2_data};
        x_rd_data = product[63:32];
      end

      INSN_MULHSU: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        product = { {32{x_rs1_data[31]}}, x_rs1_data} * {32'b0, x_rs2_data};
        x_rd_data = product[63:32];
      end

      INSN_MULHU: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        product = x_rs1_data * x_rs2_data;
        x_rd_data = product[63:32];
      end

      INSN_DIV: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        if (x_rs1_data[31]) x = ~x_rs1_data + 1;
        if (x_rs2_data[31]) y = ~x_rs2_data + 1;
        x_rd_type = x_rs1_data[31] != x_rs2_data[31] && x_rs2_data != 0 ? 
          RD_MINUS_QUOTIENT : RD_QUOTIENT;
      end

      INSN_DIVU: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_type = RD_QUOTIENT;
      end

      INSN_REM: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        if (x_rs1_data[31]) x = ~x_rs1_data + 1;
        if (x_rs2_data[31]) y = ~x_rs2_data + 1;
        x_rd_type = x_rs1_data[31] ? RD_MINUS_REMAINDER : RD_REMAINDER;
      end

      INSN_REMU: begin
        x_reg_we = 1;
        x_rd = x_state_rd;
        x_rd_type = RD_REMAINDER;
      end
      
    endcase 
  end

  /****************/
  /* MEMORY STAGE */
  /****************/

  always_ff @(posedge clk) begin
    if (rst) begin
      m_state_pc <= 0;
      m_state_insn <= 0;
      m_state_cycle_status <= CYCLE_RESET;
      m_state_rd <= 0;
      m_state_rs2 <= 0;
      m_state_rd_data <= 0;
      m_state_rd_type <= RD_NORMAL;
      m_state_rs2_data <= 0;
      m_state_insn_type <= INSN_NOP;
      m_state_addr_to_dmem <= 0;
      m_state_reg_we <= 0;
      m_state_halt <= 0;
    end else begin
      m_state_pc <= x_state_pc;
      m_state_insn <= x_state_insn;
      m_state_cycle_status <= x_state_cycle_status;
      m_state_rd <= x_rd;
      m_state_rs2 <= x_state_rs2;
      m_state_rd_data <= x_rd_data;
      m_state_rd_type <= x_rd_type;
      m_state_rs2_data <= x_rs2_data;
      m_state_insn_type <= x_state_insn_type;
      m_state_addr_to_dmem <= x_addr_to_dmem;
      m_state_reg_we <= x_reg_we;
      m_state_halt <= x_halt;
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_memory (
      .insn  (m_state_insn),
      .disasm(m_disasm)
  );
  
  logic [31:0] m_rs2_data;
  logic w_is_load;
  // WM bypass  
  always_comb begin
    w_is_load = w_state_insn_type == INSN_LB || w_state_insn_type == INSN_LH ||
      w_state_insn_type == INSN_LW || w_state_insn_type == INSN_LBU || 
      w_state_insn_type == INSN_LHU;
    m_rs2_data = m_state_rs2_data;
    if (m_state_rs2 == w_state_rd && w_is_load && m_is_store)
      m_rs2_data = w_rd_data;
  end 

  logic [31:0] m_rd_data;
  logic [31:0] m_read_addr;
  logic [31:0] m_write_addr;

  always_comb begin
    m_read_addr = 0;
    m_write_addr = 0;

    dmem.WSTRB = 0;
    dmem.WVALID = 0;
    dmem.AWVALID = 0;
    dmem.BREADY = 0;

    case (m_state_insn_type)

      INSN_LB: m_read_addr = {m_state_addr_to_dmem[31:2], 2'b0};
      INSN_LH: m_read_addr = {m_state_addr_to_dmem[31:2], 2'b0};
      INSN_LW: m_read_addr = {m_state_addr_to_dmem[31:2], 2'b0};
      INSN_LBU: m_read_addr = {m_state_addr_to_dmem[31:2], 2'b0};
      INSN_LHU: m_read_addr = {m_state_addr_to_dmem[31:2], 2'b0};

      INSN_SB: begin
        dmem.WVALID = 1;
        dmem.AWVALID = 1;
        dmem.BREADY = 1;
        m_write_addr = {m_state_addr_to_dmem[31:2], 2'b0};
        dmem.WSTRB = 4'b0001 << m_state_addr_to_dmem[1:0];
        dmem.WDATA = {24'b0, m_rs2_data[7:0]} << (m_state_addr_to_dmem[1:0] * 8);
      end

      INSN_SH: begin
        dmem.WVALID  = 1;
        dmem.AWVALID = 1;
        dmem.BREADY  = 1;
        m_write_addr = {m_state_addr_to_dmem[31:2], 2'b0};
        dmem.WSTRB = 4'b0011 << m_state_addr_to_dmem[1:0];
        dmem.WDATA = {16'b0, m_rs2_data[15:0]} << (m_state_addr_to_dmem[1:0] * 8);
      end

      INSN_SW: begin
        dmem.WVALID  = 1;
        dmem.AWVALID = 1;
        dmem.BREADY  = 1;
        m_write_addr = {m_state_addr_to_dmem[31:2], 2'b0};
        dmem.WSTRB = 4'b1111 << m_state_addr_to_dmem[1:0];
        dmem.WDATA = m_rs2_data << (m_state_addr_to_dmem[1:0] * 8);
      end
      
      default: begin
        m_rd_data = m_state_rd_data;
      end
    endcase
  end

  assign dmem.ARVALID = 1;
  assign dmem.ARADDR  = m_read_addr;
  assign dmem.AWADDR  = m_write_addr;

  /*******************/
  /* WRITEBACK STAGE */
  /*******************/

  always_ff @(posedge clk) begin
    if (rst) begin
      w_state_pc <= 0;
      w_state_insn <= 0;
      w_state_cycle_status <= CYCLE_RESET;
      w_state_insn_type <= INSN_NOP;
      w_state_rd <= 0;
      w_state_rd_data <= 0;
      w_state_addr_to_dmem <= 0;
      w_state_reg_we <= 0;
      w_state_halt <= 0;
    end else begin
      w_state_pc <= m_state_pc;
      w_state_insn <= m_state_insn;
      w_state_cycle_status <= m_state_cycle_status;
      w_state_insn_type <= m_state_insn_type;
      w_state_rd <= m_state_rd;
      w_state_rd_data <= m_state_rd_type == RD_NORMAL ? m_rd_data :
        m_state_rd_type == RD_QUOTIENT ? quotient :
        m_state_rd_type == RD_MINUS_QUOTIENT ? ~quotient + 1 :
        m_state_rd_type == RD_REMAINDER ? remainder : ~remainder + 1;
      w_state_addr_to_dmem <= m_state_addr_to_dmem;
      w_state_reg_we <= m_state_reg_we;
      w_state_halt <= m_state_halt;
    end
  end
  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_writeback (
      .insn  (w_state_insn),
      .disasm(w_disasm)
  );

  logic [31:0] w_rd_data;
  
  always_comb begin
  
    w_rd_data = w_state_rd_data;

    case (w_state_insn_type)
    
      INSN_LB: begin
        case (w_state_addr_to_dmem[1:0])
          2'b00: w_rd_data = {{24{dmem.RDATA[7]}}, dmem.RDATA[7:0]};
          2'b01: w_rd_data = {{24{dmem.RDATA[15]}}, dmem.RDATA[15:8]};
          2'b10: w_rd_data = {{24{dmem.RDATA[23]}}, dmem.RDATA[23:16]};
          2'b11: w_rd_data = {{24{dmem.RDATA[31]}}, dmem.RDATA[31:24]};
        endcase
      end
      
      INSN_LH: begin
        case (w_state_addr_to_dmem[1])
          0: w_rd_data = {{16{dmem.RDATA[15]}}, dmem.RDATA[15:0]};
          1: w_rd_data = {{16{dmem.RDATA[31]}}, dmem.RDATA[31:16]};
        endcase
      end
      
      INSN_LW: w_rd_data = dmem.RDATA; 

      INSN_LBU: begin
        case (w_state_addr_to_dmem[1:0])
          2'b00: w_rd_data = {24'b0, dmem.RDATA[7:0]};
          2'b01: w_rd_data = {24'b0, dmem.RDATA[15:8]};
          2'b10: w_rd_data = {24'b0, dmem.RDATA[23:16]};
          2'b11: w_rd_data = {24'b0, dmem.RDATA[31:24]};
        endcase
      end

      INSN_LHU: begin
        case (w_state_addr_to_dmem[1])
          0: w_rd_data = {16'b0, dmem.RDATA[15:0]};
          1: w_rd_data = {16'b0, dmem.RDATA[31:16]};
        endcase
      end

    endcase
  end

  assign trace_writeback_pc = w_state_pc;
  assign trace_writeback_insn = w_state_insn;
  assign trace_writeback_cycle_status = w_state_cycle_status;

  assign halt = w_state_halt;

endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  // HW6 memory interface
  axi_clkrst_if axi_cr (
      .ACLK(clk),
      .ARESETn(~rst)
  );
  axi_if axi_data ();
  axi_if axi_insn ();
  MemoryAxiLite #(
      .NUM_WORDS(8192)
  ) mem (
      .axi (axi_cr),
      .insn(axi_insn.subord),
      .data(axi_data.subord)
  );

  DatapathAxilMemory datapath (
      .clk(clk),
      .rst(rst),
      .imem(axi_insn.manager),
      .dmem(axi_data.manager),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
