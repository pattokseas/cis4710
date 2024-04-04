`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

// size of the wire to track insn name (6 bits)
`define INSN_NAME_SIZE 5:0

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
  CYCLE_DIV2USE  = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI   = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

/** execute state **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  logic [4:0] rs1;
  logic [4:0] rs2;
  logic [4:0] rd;

  logic [19:0] imm_u;
  logic [4:0] imm_i_4_0;
  logic [`REG_SIZE] imm_i_sext;
  logic [`REG_SIZE] imm_b_sext;

  logic [`INSN_NAME_SIZE] insn_name;
} stage_execute_t;

/** memory state **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  logic [4:0] rd;
  logic [`REG_SIZE] rd_data;

  logic we;
  logic halt;
} stage_memory_t;

/** writeback state **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  logic [4:0] rd;
  logic [`REG_SIZE] rd_data;

  logic we;
  logic halt;
} stage_writeback_t;


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

  /***********/
  /* MODULES */
  /***********/

  // The insn in the execute stage is READING from
  // the register file, while the insn in the writeback stage
  // is WRITING to the register file
  RegFile rf (
      .rd(writeback_state.rd),
      .rd_data(w_rd_data),
      .rs1(execute_state.rs1),
      .rs1_data(x_rs1_data),
      .rs2(execute_state.rs2),
      .rs2_data(x_rs2_data),

      .clk(clk),
      .we (w_we),
      .rst(rst)
  );

  // opcodes - see section 19 of RiscV spec
  // localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  // localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  // localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  // localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  // localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  // localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  // localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  // localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  // localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  // localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  // localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

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
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current   <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (x_branching) begin
      f_pc_current   <= x_branch_pc;
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current   <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

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
      decode_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_RESET};
    end else if (x_branching) begin
      decode_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_TAKEN_BRANCH};
    end else begin
      begin
        decode_state <= '{pc: f_pc_current, insn: f_insn, cycle_status: f_cycle_status};
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

  // components of the instruction
  wire [6:0] d_insn_funct7;
  wire [2:0] d_insn_funct3;
  wire [4:0] d_insn_rs1;
  wire [4:0] d_insn_rs2;
  wire [4:0] d_insn_rd;
  wire [`OPCODE_SIZE] d_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd, d_insn_opcode} = decode_state.insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] d_imm_i;
  assign d_imm_i = decode_state.insn[31:20];
  wire [ 4:0] d_imm_shamt = decode_state.insn[24:20];
  wire [ 4:0] d_imm_i_4_0 = d_imm_i[4:0];

  // S - stores
  wire [11:0] d_imm_s;
  assign d_imm_s[11:5] = d_insn_funct7, d_imm_s[4:0] = d_insn_rd;

  // B - conditionals
  wire [12:0] d_imm_b;
  assign {d_imm_b[12], d_imm_b[10:5]} = d_insn_funct7,
      {d_imm_b[4:1], d_imm_b[11]} = d_insn_rd,
      d_imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] d_imm_j;
  assign {d_imm_j[20], d_imm_j[10:1], d_imm_j[11], d_imm_j[19:12], d_imm_j[0]} = {
    decode_state.insn[31:12], 1'b0
  };

  // U - setup for U type instructions
  wire [19:0] d_imm_u;
  assign d_imm_u = decode_state.insn[31:12];

  wire [`REG_SIZE] d_imm_i_sext = {{20{d_imm_i[11]}}, d_imm_i[11:0]};
  wire [`REG_SIZE] d_imm_s_sext = {{20{d_imm_s[11]}}, d_imm_s[11:0]};
  wire [`REG_SIZE] d_imm_b_sext = {{19{d_imm_b[12]}}, d_imm_b[12:0]};
  wire [`REG_SIZE] d_imm_j_sext = {{11{d_imm_j[20]}}, d_imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire d_insn_lui = d_insn_opcode == OpLui;
  wire d_insn_auipc = d_insn_opcode == OpAuipc;
  wire d_insn_jal = d_insn_opcode == OpJal;
  wire d_insn_jalr = d_insn_opcode == OpJalr;

  wire d_insn_beq = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b000;
  wire d_insn_bne = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b001;
  wire d_insn_blt = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b100;
  wire d_insn_bge = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b101;
  wire d_insn_bltu = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b110;
  wire d_insn_bgeu = d_insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b111;

  wire d_insn_lb = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b000;
  wire d_insn_lh = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b001;
  wire d_insn_lw = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b010;
  wire d_insn_lbu = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b100;
  wire d_insn_lhu = d_insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b101;

  wire d_insn_sb = d_insn_opcode == OpStore && decode_state.insn[14:12] == 3'b000;
  wire d_insn_sh = d_insn_opcode == OpStore && decode_state.insn[14:12] == 3'b001;
  wire d_insn_sw = d_insn_opcode == OpStore && decode_state.insn[14:12] == 3'b010;

  wire d_insn_addi = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b000;
  wire d_insn_slti = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b010;
  wire d_insn_sltiu = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b011;
  wire d_insn_xori = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b100;
  wire d_insn_ori = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b110;
  wire d_insn_andi = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b111;

  wire d_insn_slli = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b001 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_srli = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_srai = d_insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'b0100000;

  wire d_insn_add = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b000 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_sub  = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b000 && decode_state.insn[31:25] == 7'b0100000;
  wire d_insn_sll = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b001 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_slt = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b010 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_sltu = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b011 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_xor = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b100 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_srl = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_sra  = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'b0100000;
  wire d_insn_or = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b110 && decode_state.insn[31:25] == 7'd0;
  wire d_insn_and = d_insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b111 && decode_state.insn[31:25] == 7'd0;

  wire d_insn_mul    = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b000;
  wire d_insn_mulh   = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b001;
  wire d_insn_mulhsu = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b010;
  wire d_insn_mulhu  = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b011;
  wire d_insn_div    = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b100;
  wire d_insn_divu   = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b101;
  wire d_insn_rem    = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b110;
  wire d_insn_remu   = d_insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b111;

  wire d_insn_ecall = d_insn_opcode == OpEnviron && decode_state.insn[31:7] == 25'd0;
  wire d_insn_fence = d_insn_opcode == OpMiscMem;

  logic [5:0] d_insn_name;
  localparam bit [5:0] InsnLui = 6'd1;
  localparam bit [5:0] InsnAuipc = 6'd2;
  localparam bit [5:0] InsnJal = 6'd3;
  localparam bit [5:0] InsnJalr = 6'd4;
  localparam bit [5:0] InsnBeq = 6'd5;
  localparam bit [5:0] InsnBne = 6'd6;
  localparam bit [5:0] InsnBlt = 6'd7;
  localparam bit [5:0] InsnBge = 6'd8;
  localparam bit [5:0] InsnBltu = 6'd9;
  localparam bit [5:0] InsnBgeu = 6'd10;
  localparam bit [5:0] InsnLb = 6'd11;
  localparam bit [5:0] InsnLh = 6'd12;
  localparam bit [5:0] InsnLw = 6'd13;
  localparam bit [5:0] InsnLbu = 6'd14;
  localparam bit [5:0] InsnLhu = 6'd15;
  localparam bit [5:0] InsnSb = 6'd16;
  localparam bit [5:0] InsnSh = 6'd17;
  localparam bit [5:0] InsnSw = 6'd18;
  localparam bit [5:0] InsnAddi = 6'd19;
  localparam bit [5:0] InsnSlti = 6'd20;
  localparam bit [5:0] InsnSltiu = 6'd21;
  localparam bit [5:0] InsnXori = 6'd22;
  localparam bit [5:0] InsnOri = 6'd23;
  localparam bit [5:0] InsnAndi = 6'd24;
  localparam bit [5:0] InsnSlli = 6'd25;
  localparam bit [5:0] InsnSrli = 6'd26;
  localparam bit [5:0] InsnSrai = 6'd27;
  localparam bit [5:0] InsnAdd = 6'd28;
  localparam bit [5:0] InsnSub = 6'd29;
  localparam bit [5:0] InsnSll = 6'd30;
  localparam bit [5:0] InsnSlt = 6'd31;
  localparam bit [5:0] InsnSltu = 6'd32;
  localparam bit [5:0] InsnXor = 6'd33;
  localparam bit [5:0] InsnSrl = 6'd34;
  localparam bit [5:0] InsnSra = 6'd35;
  localparam bit [5:0] InsnOr = 6'd36;
  localparam bit [5:0] InsnAnd = 6'd37;
  localparam bit [5:0] InsnMul = 6'd38;
  localparam bit [5:0] InsnMulh = 6'd39;
  localparam bit [5:0] InsnMulhsu = 6'd40;
  localparam bit [5:0] InsnMulhu = 6'd41;
  localparam bit [5:0] InsnDiv = 6'd42;
  localparam bit [5:0] InsnDivu = 6'd43;
  localparam bit [5:0] InsnRem = 6'd44;
  localparam bit [5:0] InsnRemu = 6'd45;
  localparam bit [5:0] InsnEcall = 6'd46;
  localparam bit [5:0] InsnFence = 6'd47;

  assign d_insn_name = d_insn_lui ? InsnLui : 
    (d_insn_auipc ? InsnAuipc : 
    (d_insn_jal ? InsnJal : 
    (d_insn_jalr ? InsnJalr :
    (d_insn_beq ? InsnBeq :
    (d_insn_bne ? InsnBne :
    (d_insn_blt ? InsnBlt :
    (d_insn_bge ? InsnBge :
    (d_insn_bltu ? InsnBltu :
    (d_insn_bgeu ? InsnBgeu :
    (d_insn_lb ? InsnLb :
    (d_insn_lh ? InsnLh :
    (d_insn_lw ? InsnLw :
    (d_insn_lbu ? InsnLbu :
    (d_insn_lhu ? InsnLhu :
    (d_insn_sb ? InsnSb :
    (d_insn_sh ? InsnSh :
    (d_insn_sw ? InsnSw :
    (d_insn_addi ? InsnAddi :
    (d_insn_slti ? InsnSlti :
    (d_insn_sltiu ? InsnSltiu :
    (d_insn_xori ? InsnXori :
    (d_insn_ori ? InsnOri :
    (d_insn_andi ? InsnAndi :
    (d_insn_slli ? InsnSlli :
    (d_insn_srli ? InsnSrli :
    (d_insn_srai ? InsnSrai :
    (d_insn_add ? InsnAdd :
    (d_insn_sub ? InsnSub :
    (d_insn_sll ? InsnSll :
    (d_insn_slt ? InsnSlt :
    (d_insn_sltu ? InsnSltu :
    (d_insn_xor ? InsnXor :
    (d_insn_srl ? InsnSrl :
    (d_insn_sra ? InsnSra :
    (d_insn_or ? InsnOr :
    (d_insn_and ? InsnAnd :
    (d_insn_mul ? InsnMul :
    (d_insn_mulh ? InsnMulh :
    (d_insn_mulhsu ? InsnMulhsu :
    (d_insn_mulhu ? InsnMulhu :
    (d_insn_div ? InsnDiv :
    (d_insn_divu ? InsnDivu :
    (d_insn_rem ? InsnRem :
    (d_insn_remu ? InsnRemu :
    (d_insn_ecall ? InsnEcall :
    (d_insn_fence ? InsnFence : 6'd0
    ))))))))))))))))))))))))))))))))))))))))))))));

  /*****************/
  /* EXECUTE STAGE */
  /*****************/

  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,

          rs1: 0,
          rs2: 0,
          rd: 0,

          imm_u: 0,
          imm_i_4_0: 0,
          imm_i_sext: 0,
          imm_b_sext: 0,

          insn_name: 0
      };
    end else if (x_branching) begin
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_TAKEN_BRANCH,

          rs1: 0,
          rs2: 0,
          rd: 0,

          imm_u: 0,
          imm_i_4_0: 0,
          imm_i_sext: 0,
          imm_b_sext: 0,

          insn_name: 0
      };
    end else begin
      begin
        execute_state <= '{
            pc: decode_state.pc,
            insn: decode_state.insn,
            cycle_status: decode_state.cycle_status,

            rs1: d_insn_rs1,
            rs2: d_insn_rs2,
            rd: d_insn_rd,

            imm_u: d_imm_u,
            imm_i_4_0: d_imm_i_4_0,
            imm_i_sext: d_imm_i_sext,
            imm_b_sext: d_imm_b_sext,

            insn_name: d_insn_name
        };
      end
    end
  end
  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_2execute (
      .insn  (execute_state.insn),
      .disasm(x_disasm)
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

  // // //
  // EXECUTE: Modules Used
  // // //

  logic [4:0] x_rs1, x_rd;
  logic [`REG_SIZE] x_rd_data_inter;
  logic [`REG_SIZE] x_rd_data, x_rs1_data, x_rs2_data;
  logic [4:0] x_rs2_data_4_0;

  logic x_we;
  logic x_halt;

  // For branching
  logic [`REG_SIZE] x_branch_pc;
  logic x_branching;

  // MX and WX bypassing
  // - First we check for a MX bypass, i.e. if x-rs1 = m-rd
  // - Otherwise, we check for a WX bypass, i.e. if x-rs1 = w-rd
  // - Otherwise, we just use the value we got from the register file
  logic [`REG_SIZE] x_bp_rs1_data, x_bp_rs2_data;
  assign x_bp_rs1_data = ((execute_state.rs1 == memory_state.rd) && (execute_state.rs1 != 0)) ? memory_state.rd_data : (
    ((execute_state.rs1 == writeback_state.rd) && (execute_state.rs1 != 0)) ? writeback_state.rd_data : x_rs1_data
  );
  assign x_bp_rs2_data = ((execute_state.rs2 == memory_state.rd) && (execute_state.rs2 != 0)) ? memory_state.rd_data : (
    ((execute_state.rs2 == writeback_state.rd) && (execute_state.rs2 != 0)) ? writeback_state.rd_data : x_rs2_data
  );
  assign x_rs2_data_4_0 = x_bp_rs2_data[4:0];

  // CLA stuff
  logic [`REG_SIZE] x_cla_a, x_cla_b;

  cla x_cla (
      .a  (x_cla_a),
      .b  (x_cla_b),
      .cin(1'b0),
      .sum(x_rd_data_inter)
  );

  logic [`REG_SIZE] x_cla_inc_in, x_cla_inc_out;
  logic [`REG_SIZE] x_cla_one = 32'b1;

  cla x_cla_incr (
      .a  (x_cla_inc_in),
      .b  (x_cla_one),
      .cin(1'b0),
      .sum(x_cla_inc_out)
  );

  // // //
  // EXECUTE: Logic
  // // //

  always_comb begin
    x_rd = 0;
    x_rd_data = 0;
    x_we = 0;
    x_cla_inc_in = 0;
    x_cla_a = 0;
    x_cla_b = 0;

    x_halt = 0;

    // Branching
    x_branching = 0;
    x_branch_pc = execute_state.pc;

    case (execute_state.insn_name)

      // Arithmetic Insns

      InsnLui: begin
        x_rd = execute_state.rd;
        x_rd_data = {execute_state.imm_u, 12'b0};
        x_we = 1;
      end

      InsnAddi: begin
        x_cla_a = x_bp_rs1_data;
        x_cla_b = execute_state.imm_i_sext;

        x_rd = execute_state.rd;
        x_rd_data = x_rd_data_inter;
        x_we = 1;
      end

      InsnSlti: begin
        x_rd = execute_state.rd;
        x_rd_data = $signed(x_bp_rs1_data) < $signed(execute_state.imm_i_sext) ? 1 : 0;
        x_we = 1;
      end

      InsnSltiu: begin
        x_rd = execute_state.rd;
        x_rd_data = $unsigned(x_bp_rs1_data) < $unsigned(execute_state.imm_i_sext) ? 1 : 0;
        x_we = 1;
      end

      InsnXori: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data ^ execute_state.imm_i_sext;
        x_we = 1;
      end

      InsnOri: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data | execute_state.imm_i_sext;
        x_we = 1;
      end

      InsnAndi: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data & execute_state.imm_i_sext;
        x_we = 1;
      end

      InsnSlli: begin
        // Note: To fix this I implemented a new thing in decode/execute stage: d_imm_i_4_0. in decode stage it takes [4:0] from d_imm_i

        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data << execute_state.imm_i_4_0;
        x_we = 1;
      end

      InsnSrli: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data >> execute_state.imm_i_4_0;
        x_we = 1;
      end

      InsnSrai: begin
        x_rd = execute_state.rd;
        x_rd_data = $signed(x_bp_rs1_data) >>> execute_state.imm_i_4_0;
        x_we = 1;
      end

      InsnSltu: begin
        x_rd = execute_state.rd;
        x_rd_data = $unsigned(x_bp_rs1_data) < $unsigned(x_bp_rs2_data) ? 1 : 0;
        x_we = 1;
      end

      InsnAdd: begin
        x_cla_a = x_bp_rs1_data;
        x_cla_b = x_bp_rs2_data;
        x_cla_inc_in = 0;

        x_rd = execute_state.rd;
        x_rd_data = x_rd_data_inter;
        x_we = 1;
      end

      InsnSub: begin
        x_cla_inc_in = ~x_bp_rs2_data;  // invert all the bits
        x_cla_b = x_cla_inc_out;  // add 1

        x_cla_a = x_bp_rs1_data;
        x_cla_b = x_cla_inc_out;
        x_cla_inc_in = ~x_bp_rs2_data;

        x_rd = execute_state.rd;
        x_rd_data = x_rd_data_inter;
        x_we = 1;
      end

      InsnAnd: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data & x_bp_rs2_data;
        x_we = 1;
      end

      InsnOr: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data | x_bp_rs2_data;
        x_we = 1;
      end

      InsnXor: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data ^ x_bp_rs2_data;
        x_we = 1;
      end

      InsnSlt: begin
        x_rd = execute_state.rd;
        x_rd_data = $signed(x_bp_rs1_data) < $signed(x_bp_rs2_data) ? 1 : 0;
        x_we = 1;
      end

      InsnSll: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data << x_rs2_data_4_0;
        x_we = 1;
      end

      InsnSrl: begin
        x_rd = execute_state.rd;
        x_rd_data = x_bp_rs1_data >> x_rs2_data_4_0;
        x_we = 1;
      end

      InsnSra: begin
        x_rd = execute_state.rd;
        x_rd_data = $signed(x_bp_rs1_data) >>> x_rs2_data_4_0;
        x_we = 1;
      end



      // Branch Insns

      /* 
        On a taken branch, your datapath will flush the instructions in Fetch and Decode 
        (replacing them with NOPs/bubbles) and then fetch the correct-path instruction 
        in the following cycle (when the branch moves to the Memory stage). The pipelining 
        lecture slides discuss the cycle timing in detail.
      */

      InsnBeq: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;

        if (x_bp_rs1_data == x_bp_rs2_data) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBne: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;

        if (x_bp_rs1_data != x_bp_rs2_data) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBlt: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;

        if ($signed(x_bp_rs1_data) < $signed(x_bp_rs2_data)) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBge: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;
        if ($signed(x_bp_rs1_data) >= $signed(x_bp_rs2_data)) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBltu: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;
        if ($unsigned(x_bp_rs1_data) < $unsigned(x_bp_rs2_data)) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnBgeu: begin
        x_rd = 0;
        x_rd_data = 0;
        x_we = 0;
        if ($unsigned(x_bp_rs1_data) >= $unsigned(x_bp_rs2_data)) begin
          x_branch_pc = execute_state.pc + execute_state.imm_b_sext;
          x_branching = 1;
        end
      end

      InsnFence: begin
        x_we = 0;
      end

      InsnEcall: begin
        x_we   = 0;
        x_halt = 1;
      end

      default: begin
        x_we = 0;
      end
    endcase
  end

  /****************/
  /* MEMORY STAGE */
  /****************/

  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,

          rd: 0,
          rd_data: 0,

          we: 0,
          halt: 0
      };
    end else begin
      begin
        memory_state <= '{
            pc: execute_state.pc,  // Even if we branch, we should propagate the old pc here
            insn: execute_state.insn,
            cycle_status: execute_state.cycle_status,

            rd: x_rd,
            rd_data: x_rd_data,

            we: x_we,
            halt: x_halt
        };
      end
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_3memory (
      .insn  (execute_state.insn),
      .disasm(m_disasm)
  );

  /*******************/
  /* WRITEBACK STAGE */
  /*******************/

  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,

          rd: 0,
          rd_data: 0,

          we: memory_state.we,
          halt: memory_state.halt
      };
    end else begin
      begin
        writeback_state <= '{
            pc: memory_state.pc,
            insn: memory_state.insn,
            cycle_status: memory_state.cycle_status,

            rd: memory_state.rd,
            rd_data: memory_state.rd_data,

            we: memory_state.we,
            halt: memory_state.halt
        };
      end
    end
  end
  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_4writeback (
      .insn  (memory_state.insn),
      .disasm(w_disasm)
  );

  // Traces
  assign trace_writeback_pc = writeback_state.pc;
  assign trace_writeback_insn = writeback_state.insn;
  assign trace_writeback_cycle_status = writeback_state.cycle_status;

  logic w_we;
  logic [`REG_SIZE] w_rd_data;

  // Writing back to register files
  always_comb begin
    if (writeback_state.we == 1) begin
      w_rd_data = writeback_state.rd_data;
      w_we = writeback_state.we;
    end else begin
      w_rd_data = 0;
      w_we = 0;
    end

    // More instructions here...


    // Set halt appropriately
    halt = writeback_state.halt;
  end
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
