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
  genvar i;
  logic [`REG_SIZE] regs[NumRegs];


    assign regs[0] = 32'd0;  // zero always zero

    assign rs1_data = (we == 1 && rs1 == rd && rd != 0) ? rd_data : regs[rs1]; // read registers
    assign rs2_data = (we == 1 && rs2 == rd && rd != 0) ? rd_data : regs[rs2];
    
    for(i = 1; i < NumRegs; i = i + 1) begin  // make DFFs for R1-R31
        always_ff @(posedge clk) begin                                                                                                                                                        
            if(rst) regs[i] <= 32'b0;              // reset
        else if(we && rd == i) regs[i] <= rd_data; // write
        end
    end 


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

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

typedef enum {
  INSN_NOP,
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
} insn_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  insn_t insn_type;
  logic [4:0] rs1;
  logic [4:0] rs2;
  logic [4:0] rd;
  logic [31:0] imm_u_shifted;
  logic [31:0] imm_i_sext;
  logic [31:0] imm_b_sext;
  logic [31:0] imm_j_sext;
  logic [31:0] imm_s_sext;
} execute_state_t;

typedef enum {
  RD_NORMAL,
  RD_QUOTIENT,
  RD_MINUS_QUOTIENT,
  RD_REMAINDER,
  RD_MINUS_REMAINDER
} rd_type_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  insn_t insn_type;
  logic [4:0] rs2;
  logic [4:0] rd;
  logic reg_we;
  logic [`REG_SIZE] rd_data;
  logic [`REG_SIZE] rs2_data;
  rd_type_t rd_type;
  logic [`REG_SIZE] addr_to_dmem;
  logic halt;
} memory_state_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  insn_t insn_type;
  logic [4:0] rd;
  logic [`REG_SIZE] rd_data;
  logic reg_we;
  logic halt;
} write_state_t;

module decode_insn(input logic [`INSN_SIZE] insn,
  output insn_t insn_type,
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

module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  /*
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;
  */
  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
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

  // stall flags
  logic branch_stalling, load_stalling, div_stalling, fence_stalling; 
  logic [31:0] branching_to;
  // state structs
  execute_state_t x_state;
  memory_state_t m_state;
  write_state_t w_state;

  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (branch_stalling) begin
      f_pc_current <= branching_to;
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (load_stalling || div_stalling || fence_stalling) begin
      f_pc_current <= f_pc_current;
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = branch_stalling ? 0 : insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else if (branch_stalling) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_TAKEN_BRANCH
      };
    end else if (load_stalling || div_stalling || fence_stalling) begin
      decode_state <= '{
        pc: decode_state.pc,
        insn: decode_state.insn,
        cycle_status: decode_state.cycle_status
      };
    end else begin
      begin
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  // : your code here, though you will also need to modify some of the code above
  // : the testbench requires that your register file instance is named `rf`
  
  wire [4:0] d_rs1; wire [4:0] d_rs2; wire [4:0] d_rd;
  insn_t d_insn_type;
  wire [31:0] d_imm_u_shifted; wire [31:0] d_imm_i_sext; wire [31:0] d_imm_b_sext;
  wire [31:0] d_imm_j_sext; wire [31:0] d_imm_s_sext;
  decode_insn d_state_decode(.insn(decode_state.insn),
    .insn_type(d_insn_type),
    .rs1(d_rs1), .rs2(d_rs2), .rd(d_rd),
    .imm_u_shifted(d_imm_u_shifted), .imm_i_sext(d_imm_i_sext), .imm_b_sext(d_imm_b_sext),
    .imm_j_sext(d_imm_j_sext), .imm_s_sext(d_imm_s_sext)
  );

  // load, divide, fence stalls
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
    x_is_load = x_state.insn_type == INSN_LB || x_state.insn_type == INSN_LH ||
      x_state.insn_type == INSN_LW || x_state.insn_type == INSN_LBU ||
      x_state.insn_type == INSN_LHU;
    x_is_div = x_state.insn_type == INSN_DIV || x_state.insn_type == INSN_DIVU ||
      x_state.insn_type == INSN_REM || x_state.insn_type == INSN_REMU;
    x_is_store = x_state.insn_type == INSN_SB || 
      x_state.insn_type == INSN_SH || x_state.insn_type == INSN_SW;
    m_is_store = m_state.insn_type == INSN_SB ||
      m_state.insn_type == INSN_SH || m_state.insn_type == INSN_SW;
    load_stalling =
      (x_is_load && x_state.rd == d_rs1 && d_rs1 != 0 && d_uses_rs1) ||
      (x_is_load && x_state.rd == d_rs2 && d_rs2 != 0 && d_uses_rs2 && ~d_is_store);
    div_stalling = 
      (x_is_div && x_state.rd == d_rs1 && d_rs1 != 0 && d_uses_rs1) ||
      (x_is_div && x_state.rd == d_rs2 && d_rs2 != 0 && d_uses_rs2);
    fence_stalling =  d_insn_type == INSN_FENCE && (x_is_store || m_is_store);
  end


  /*****************/
  /* EXECUTE STAGE */
  /*****************/

  always_ff @(posedge clk) begin
    if (rst) begin
      x_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        rs1: 0,
        rs2: 0,
        rd: 0,
        insn_type: INSN_NOP,
        imm_u_shifted: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else if (branch_stalling) begin
      x_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_TAKEN_BRANCH,
        rs1: 0,
        rs2: 0,
        rd: 0,
        insn_type: INSN_NOP,
        imm_u_shifted: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else if (load_stalling) begin
      x_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_LOAD2USE,
        rs1: 0,
        rs2: 0,
        rd: 0,
        insn_type: INSN_NOP,
        imm_u_shifted: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else if (div_stalling) begin
      x_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_DIV2USE,
        rs1: 0,
        rs2: 0,
        rd: 0,
        insn_type: INSN_NOP,
        imm_u_shifted: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else if (fence_stalling) begin
      x_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_FENCEI,
        rs1: 0,
        rs2: 0,
        rd: 0,
        insn_type: INSN_NOP,
        imm_u_shifted: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else begin
      x_state <= '{
        pc: decode_state.pc,
        insn: decode_state.insn,
        cycle_status: decode_state.cycle_status,
        rs1: d_rs1,
        rs2: d_rs2,
        rd: d_rd,
        insn_type: d_insn_type,
        imm_u_shifted: d_imm_u_shifted,
        imm_i_sext: d_imm_i_sext,
        imm_b_sext: d_imm_b_sext,
        imm_j_sext: d_imm_j_sext,
        imm_s_sext: d_imm_s_sext
      };
    end
  end
  wire [255:0] x_disasm;
  Disasm #(
    .PREFIX("X")
  ) disasm_execute (
    .insn(x_state.insn),
    .disasm(x_disasm)
  );

  logic [31:0] x_rs1_rf;
  logic [31:0] x_rs2_rf;

  RegFile rf(
    .rd(w_state.rd), .rd_data(w_state.rd_data),
    .rs1(x_state.rs1), .rs1_data(x_rs1_rf),
    .rs2(x_state.rs2), .rs2_data(x_rs2_rf),
    .clk(clk), .we(w_state.reg_we), .rst(rst)
  );


  logic [31:0] x_rs1_data;
  logic [31:0] x_rs2_data;

  always_comb begin
    x_rs1_data = x_rs1_rf;
    x_rs2_data = x_rs2_rf;
    // WX bypass
    if (w_state.reg_we && w_state.rd == x_state.rs1 && x_state.rs1 != 0)
      x_rs1_data = w_state.rd_data;
    if (w_state.reg_we && w_state.rd == x_state.rs2 && x_state.rs2 != 0)
      x_rs2_data = w_state.rd_data;
    // MX bypass
    if (m_state.reg_we && m_state.rd == x_state.rs1 && x_state.rs1 != 0)
      x_rs1_data = m_state.rd_data;
    if (m_state.reg_we && m_state.rd == x_state.rs2 && x_state.rs2 != 0)
      x_rs2_data = m_state.rd_data;
  end

  logic [31:0] x; logic [31:0] y; logic [31:0] sum; 
  logic [31:0] quotient; logic [31:0] remainder;
  cla adder(.a(x), .b(y), .cin(0), .sum(sum));
  divider_unsigned_pipelined divider(
    .clk(clk), .rst(rst),
    .i_dividend(x), .i_divisor(y),
    .o_remainder(remainder), .o_quotient(quotient)
  );
  logic [63:0] product;

  rd_type_t x_rd_type;

  logic [31:0] x_rd_data;
  logic x_reg_we;
  logic [31:0] x_addr_to_dmem;

  logic x_halt;
  
  always_comb begin
    x_rd_data = 0;
    x_reg_we = 0;
    x_addr_to_dmem = 0;
    x_halt = 0;

    x_rd_type = RD_NORMAL;

    x = x_rs1_data;
    y = x_rs2_data;

    product = 0;

    branch_stalling = 0;
    branching_to = 0;

    case (x_state.insn_type)

      INSN_LUI: begin
        x_reg_we = 1;
        x_rd_data = x_state.imm_u_shifted;
      end

      INSN_AUIPC: begin
        x_reg_we = 1;
        x_rd_data = x_state.pc + x_state.imm_u_shifted;
      end

      INSN_ADDI: begin
        x_reg_we = 1;
        y = x_state.imm_i_sext;
        x_rd_data = sum;
      end

      INSN_SLTI: begin
        x_reg_we = 1;
        x_rd_data = $signed(x_rs1_data) < $signed(x_state.imm_i_sext) ? 1 : 0;
      end
      
      INSN_SLTIU: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data < x_state.imm_i_sext ? 1 : 0;
      end

      INSN_XORI: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data ^ x_state.imm_i_sext;
      end

      INSN_ORI: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data | x_state.imm_i_sext;
      end

      INSN_ANDI: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data & x_state.imm_i_sext;
      end

      INSN_SLLI: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data << x_state.imm_i_sext[4:0];
      end

      INSN_SRLI: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data >> x_state.imm_i_sext[4:0];
      end

      INSN_SRAI: begin
        x_reg_we = 1;
        x_rd_data = $signed(x_rs1_data) >>> x_state.imm_i_sext[4:0];
      end

      INSN_ADD: begin
        x_reg_we = 1;
        x_rd_data = sum;
      end

      INSN_SUB: begin
        x_reg_we = 1;
        y = ~x_rs2_data + 1;
        x_rd_data = sum;
      end

      INSN_SLL: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data << x_rs2_data[4:0];
      end

      INSN_SLT: begin
        x_reg_we = 1;
        x_rd_data = $signed(x_rs1_data) < $signed(x_rs2_data) ? 1 : 0;
      end

      INSN_SLTU: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data < x_rs2_data ? 1 : 0;
      end

      INSN_XOR: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data ^ x_rs2_data;
      end

      INSN_SRL: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data >> x_rs2_data[4:0];
      end

      INSN_SRA: begin
        x_reg_we = 1;
        x_rd_data = $signed(x_rs1_data) >>> x_rs2_data[4:0];
      end

      INSN_OR: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data | x_rs2_data;
      end

      INSN_AND: begin
        x_reg_we = 1;
        x_rd_data = x_rs1_data & x_rs2_data;
      end

      INSN_LB: begin
        x_reg_we = 1;
        x_addr_to_dmem = x_rs1_data + x_state.imm_i_sext;
      end

      INSN_LH: begin
        x_reg_we = 1;
        x_addr_to_dmem = x_rs1_data + x_state.imm_i_sext;
      end

      INSN_LW: begin
        x_reg_we = 1;
        x_addr_to_dmem = x_rs1_data + x_state.imm_i_sext;
      end

      INSN_LBU: begin
        x_reg_we = 1;
        x_addr_to_dmem = x_rs1_data + x_state.imm_i_sext;
      end

      INSN_LHU: begin
        x_reg_we = 1;
        x_addr_to_dmem = x_rs1_data + x_state.imm_i_sext;
      end

      INSN_SB: begin
        x_addr_to_dmem = x_rs1_data + x_state.imm_s_sext;
      end

      INSN_SH: begin
        x_addr_to_dmem = x_rs1_data + x_state.imm_s_sext;
      end

      INSN_SW: begin
        x_addr_to_dmem = x_rs1_data + x_state.imm_s_sext;
      end

      INSN_JAL: begin
        x_reg_we = 1;
        x_rd_data = x_state.pc + 4;
        branch_stalling = 1;
        branching_to = x_state.pc + x_state.imm_j_sext;
      end

      INSN_JALR: begin
        x_reg_we = 1;
        x_rd_data = x_state.pc + 4;
        branch_stalling = 1;
        branching_to = (x_rs1_data + x_state.imm_i_sext) & ~32'b1;
      end

      INSN_BEQ: begin
        if (x_rs1_data == x_rs2_data) begin
          branch_stalling = 1;
          branching_to = x_state.pc + x_state.imm_b_sext;
        end
      end 

      INSN_BNE: begin
        if (x_rs1_data != x_rs2_data) begin
          branch_stalling = 1;
          branching_to = x_state.pc + x_state.imm_b_sext;
        end 
      end 

      INSN_BLT: begin
        if ($signed(x_rs1_data) < $signed(x_rs2_data)) begin
          branch_stalling = 1;
          branching_to = x_state.pc + x_state.imm_b_sext;
        end 
      end 

      INSN_BGE: begin
        if ($signed(x_rs1_data) >= $signed(x_rs2_data)) begin
          branch_stalling = 1;
          branching_to = x_state.pc + x_state.imm_b_sext;
        end 
      end 

      INSN_BLTU: begin
        if (x_rs1_data < x_rs2_data) begin
          branch_stalling = 1;
          branching_to = x_state.pc + x_state.imm_b_sext;
        end 
      end 

      INSN_BGEU: begin
        if (x_rs1_data >= x_rs2_data) begin
          branch_stalling = 1;
          branching_to = x_state.pc + x_state.imm_b_sext;
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
        x_rd_data = x_rs1_data * x_rs2_data;
      end

      INSN_MULH: begin
        x_reg_we = 1;
        product = { {32{x_rs1_data[31]}}, x_rs1_data} * { {32{x_rs2_data[31]}}, x_rs2_data};
        x_rd_data = product[63:32];
      end

      INSN_MULHSU: begin
        x_reg_we = 1;
        product = { {32{x_rs1_data[31]}}, x_rs1_data} * {32'b0, x_rs2_data};
        x_rd_data = product[63:32];
      end

      INSN_MULHU: begin
        x_reg_we = 1;
        product = x_rs1_data * x_rs2_data;
        x_rd_data = product[63:32];
      end

      INSN_DIV: begin
        x_reg_we = 1;
        if (x_rs1_data[31]) x = ~x_rs1_data + 1;
        if (x_rs2_data[31]) y = ~x_rs2_data + 1;
        x_rd_type = x_rs1_data[31] != x_rs2_data[31] && x_rs2_data != 0 ?
            RD_MINUS_QUOTIENT : RD_QUOTIENT;
      end

      INSN_DIVU: begin
        x_reg_we = 1;
        x_rd_type = RD_QUOTIENT;
      end

      INSN_REM: begin
        x_reg_we = 1;
        if (x_rs1_data[31]) x = ~x_rs1_data + 1;
        if (x_rs2_data[31]) y = ~x_rs2_data + 1;
        x_rd_type = x_rs1_data[31] ? RD_MINUS_REMAINDER : RD_REMAINDER;
      end

      INSN_REMU: begin
        x_reg_we = 1;
        x_rd_type = RD_REMAINDER;
      end

    endcase

  end


  /****************/
  /* MEMORY STAGE */
  /****************/

  always_ff @(posedge clk) begin
    if (rst) begin
      m_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_type: INSN_NOP,
        rs2: 0,
        rd: 0,
        reg_we: 0,
        rd_data: 0,
        rs2_data: 0,
        rd_type: RD_NORMAL,
        addr_to_dmem: 0,
        halt: 0
      };
    end else begin
      m_state <= '{
        pc: x_state.pc,
        insn: x_state.insn,
        cycle_status: x_state.cycle_status,
        insn_type: x_state.insn_type,
        rs2: x_state.rs2,
        rd: x_state.rd,
        reg_we: x_reg_we,
        rd_data: x_rd_data,
        rs2_data: x_rs2_data,
        rd_type: x_rd_type,
        addr_to_dmem: x_addr_to_dmem,
        halt: x_halt
      };
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
    .PREFIX("M")
  ) disasm_memory (
    .insn(m_state.insn),
    .disasm(m_disasm)
  );

  logic [31:0] m_rs2_data;
  logic w_is_load;

  // WM bypass
  always_comb begin
    w_is_load = w_state.insn_type == INSN_LB || w_state.insn_type == INSN_LH ||
      w_state.insn_type == INSN_LW || w_state.insn_type == INSN_LBU || 
      w_state.insn_type == INSN_LHU;
    m_rs2_data = m_state.rs2_data;
    if (m_state.rs2 == w_state.rd && w_is_load && m_is_store)
      m_rs2_data = w_state.rd_data;
  end

  // load and store
  logic [31:0] m_rd_data;
  always_comb begin
    m_rd_data = m_state.rd_data;
    addr_to_dmem = 0;
    store_we_to_dmem = 4'b0000;
    
    case (m_state.insn_type)

      INSN_LB: begin
        addr_to_dmem = {m_state.addr_to_dmem[31:2], 2'b0};
        case (m_state.addr_to_dmem[1:0])
          2'b00: m_rd_data = {{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
          2'b01: m_rd_data = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
          2'b10: m_rd_data = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
          2'b11: m_rd_data = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
        endcase
      end

      INSN_LH: begin
        addr_to_dmem = {m_state.addr_to_dmem[31:2], 2'b0};
        case (m_state.addr_to_dmem[1])
          0: m_rd_data = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
          1: m_rd_data = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
        endcase
      end

      INSN_LW: begin
        addr_to_dmem = {m_state.addr_to_dmem[31:2], 2'b0};
        m_rd_data = load_data_from_dmem;
      end

      INSN_LBU: begin
        addr_to_dmem = {m_state.addr_to_dmem[31:2], 2'b0};
        case (m_state.addr_to_dmem[1:0])
          2'b00: m_rd_data = {24'b0, load_data_from_dmem[7:0]};
          2'b01: m_rd_data = {24'b0, load_data_from_dmem[15:8]};
          2'b10: m_rd_data = {24'b0, load_data_from_dmem[23:16]};
          2'b11: m_rd_data = {24'b0, load_data_from_dmem[31:24]};
        endcase
      end

      INSN_LHU: begin
        addr_to_dmem = {m_state.addr_to_dmem[31:2], 2'b0};
        case (m_state.addr_to_dmem[1])
          0: m_rd_data = {16'b0, load_data_from_dmem[15:0]};
          1: m_rd_data = {16'b0, load_data_from_dmem[31:16]};
        endcase
      end

      INSN_SB: begin
        addr_to_dmem = {m_state.addr_to_dmem[31:2], 2'b0};
        store_we_to_dmem = 4'b0001 << m_state.addr_to_dmem[1:0];
        store_data_to_dmem = (m_rs2_data & 32'hFF) << (m_state.addr_to_dmem[1:0] * 8);
      end

      INSN_SH: begin
        addr_to_dmem = {m_state.addr_to_dmem[31:2], 2'b0};
        store_we_to_dmem = 4'b0011 << m_state.addr_to_dmem[1:0];
        store_data_to_dmem = (m_rs2_data & 32'hFFFF) << (m_state.addr_to_dmem[1:0] * 8);
      end

      INSN_SW: begin
        addr_to_dmem = {m_state.addr_to_dmem[31:2], 2'b0};
        store_we_to_dmem = 4'b1111 << m_state.addr_to_dmem[1:0];
        store_data_to_dmem = m_rs2_data << (m_state.addr_to_dmem[1:0] * 8);
      end

    endcase

  end


  /*******************/
  /* WRITEBACK STAGE */
  /*******************/

  always_ff @(posedge clk) begin
    if (rst) begin
      w_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_type: INSN_NOP,
        rd: 0,
        rd_data: 0,
        reg_we: 0,
        halt: 0
      };
    end else begin
      w_state <= '{
        pc: m_state.pc,
        insn: m_state.insn,
        cycle_status: m_state.cycle_status,
        insn_type: m_state.insn_type,
        rd: m_state.rd,
        rd_data: m_state.rd_type == RD_NORMAL ? m_rd_data :
          m_state.rd_type == RD_QUOTIENT ? quotient :
          m_state.rd_type == RD_MINUS_QUOTIENT ? ~quotient + 1 :
          m_state.rd_type == RD_REMAINDER ? remainder : ~remainder + 1,
        reg_we: m_state.reg_we,
        halt: m_state.halt
      };
    end
  end
  wire [255:0] w_disasm;
  Disasm #(
    .PREFIX("W")
  ) disasm_writeback (
    .insn(w_state.insn),
    .disasm(w_disasm)
  );

  assign trace_writeback_pc = w_state.pc;
  assign trace_writeback_insn = w_state.insn;
  assign trace_writeback_cycle_status = w_state.cycle_status;

  assign halt = w_state.halt;

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
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
