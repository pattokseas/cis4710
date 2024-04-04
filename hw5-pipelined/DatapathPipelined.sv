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

  // your code here
  assign regs[0] = 32'd0;	 // zero always zero

  // read registers with WD bypass
  assign rs1_data = (we == 1 && rd == rs1 && rd != 0) ? rd_data : regs[rs1];
  assign rs2_data = (we == 1 && rd == rs2 && rd != 0) ? rd_data : regs[rs2];

  for(i = 1; i < NumRegs; i = i + 1) begin  // make DFFs for R1-R31
    always_ff @(posedge clk) begin
      if(rst) regs[i] <= 32'b0; 		       // reset
      else if(we && rd == i) regs[i] <= rd_data; // write
    end
  end

endmodule

typedef enum {
  INSN_INVALID,
  INSN_LUI, INSN_AUIPC, INSN_JAL, INSN_JALR,
  INSN_BEQ, INSN_BNE, INSN_BLT, INSN_BGE, INSN_BLTU, INSN_BGEU,
  INSN_LB, INSN_LH, INSN_LW, INSN_LBU, INSN_LHU,
  INSN_SB, INSN_SH, INSN_SW,
  INSN_ADDI, INSN_SLTI, INSN_SLTIU, INSN_XORI, INSN_ORI, INSN_ANDI,
  INSN_SLLI, INSN_SRLI, INSN_SRAI,
  INSN_ADD, INSN_SUB, INSN_SLL, INSN_SLT, INSN_SLTU, INSN_XOR, INSN_SRL, 
    INSN_SRA, INSN_OR, INSN_AND,
  INSN_MUL, INSN_MULH, INSN_MULHSU, INSN_MULHU, INSN_DIV, INSN_DIVU, INSN_REM, INSN_REMU,
  INSN_ECALL, INSN_FENCE
} insn_t;

module decode_insn(input logic [31:0] insn,
    output wire [`OPCODE_SIZE] insn_opcode,
    output wire [4:0] rs2,
    output wire [4:0] rs1,
    output wire [4:0] rd,
    output wire [11:0] imm_i,
    output wire [11:0] imm_s,
    output wire [12:0] imm_b,
    output wire [20:0] imm_j,
    output wire [31:0] imm_i_sext,
    output wire [31:0] imm_s_sext,
    output wire [31:0] imm_b_sext,
    output wire [31:0] imm_j_sext,
    output insn_t insn_type
);
  logic [6:0] funct7;
  logic [2:0] funct3;
  assign {funct7, rs2, rs1, funct3, rd, insn_opcode} = insn;
  
  assign imm_i = insn[31:20];
  assign imm_s[11:5] = funct7, imm_s[4:0] = rd;
  assign {imm_b[12], imm_b[10:5]} = funct7, {imm_b[4:1], imm_b[11]} = rd, imm_b[0] = 1'b0;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn[31:12], 1'b0};
  
  assign imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  assign imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  assign imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  assign imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  assign insn_type = 
    insn_opcode == 7'b01_101_11 ? INSN_LUI :
    insn_opcode == 7'b00_101_11 ? INSN_AUIPC :
    insn_opcode == 7'b11_011_11 ? INSN_JAL :
    insn_opcode == 7'b11_001_11 ? INSN_JALR :
    insn_opcode == 7'b11_000_11 ? ( // branch
      insn[14:12] == 3'b000 ? INSN_BEQ :
      insn[14:12] == 3'b001 ? INSN_BNE :
      insn[14:12] == 3'b100 ? INSN_BLT :
      insn[14:12] == 3'b101 ? INSN_BGE :
      insn[14:12] == 3'b110 ? INSN_BLTU :
      insn[14:12] == 3'b111 ? INSN_BGEU :
      INSN_INVALID) :
    insn_opcode == 7'b00_000_11 ? ( // load
      insn[14:12] == 3'b000 ? INSN_LB :
      insn[14:12] == 3'b001 ? INSN_LH :
      insn[14:12] == 3'b010 ? INSN_LW :
      insn[14:12] == 3'b100 ? INSN_LBU :
      insn[14:12] == 3'b101 ? INSN_LHU :
      INSN_INVALID) :
    insn_opcode == 7'b01_000_11 ? ( // store
      insn[14:12] == 3'b000 ? INSN_SB :
      insn[14:12] == 3'b001 ? INSN_SH :
      insn[14:12] == 3'b010 ? INSN_SW :
      INSN_INVALID) :
    insn_opcode == 7'b00_100_11 ? ( // reg immediate
      insn[14:12] == 3'b000 ? INSN_ADDI :
      insn[14:12] == 3'b010 ? INSN_SLTI :
      insn[14:12] == 3'b011 ? INSN_SLTIU :
      insn[14:12] == 3'b100 ? INSN_XORI :
      insn[14:12] == 3'b110 ? INSN_ORI :
      insn[14:12] == 3'b111 ? INSN_ANDI :
      insn[14:12] == 3'b001 && insn[31:25] == 7'd0 ? INSN_SLLI :
      insn[14:12] == 3'b101 && insn[31:25] == 7'd0 ? INSN_SRLI :
      insn[14:12] == 3'b101 && insn[31:25] == 7'b0100000 ? INSN_SRAI :
      INSN_INVALID) :
    insn_opcode == 7'b01_100_11 ? ( // reg reg
      insn[14:12] == 3'b000 && insn[31:25] == 7'd0 ? INSN_ADD :
      insn[14:12] == 3'b000 && insn[31:25] == 7'b0100000 ? INSN_SUB :
      insn[14:12] == 3'b001 && insn[31:25] == 7'd0 ? INSN_SLL :
      insn[14:12] == 3'b010 && insn[31:25] == 7'd0 ? INSN_SLT :
      insn[14:12] == 3'b011 && insn[31:25] == 7'd0 ? INSN_SLTU :
      insn[14:12] == 3'b100 && insn[31:25] == 7'd0 ? INSN_XOR :
      insn[14:12] == 3'b101 && insn[31:25] == 7'd0 ? INSN_SRL :
      insn[14:12] == 3'b101 && insn[31:25] == 7'b0100000 ? INSN_SRA :
      insn[14:12] == 3'b110 && insn[31:25] == 7'd0 ? INSN_OR :
      insn[14:12] == 3'b111 && insn[31:25] == 7'd0 ? INSN_AND :
      insn[14:12] == 3'b000 && insn[31:25] == 7'd1 ? INSN_MUL :
      insn[14:12] == 3'b001 && insn[31:25] == 7'd1 ? INSN_MULH :
      insn[14:12] == 3'b010 && insn[31:25] == 7'd1 ? INSN_MULHSU : 
      insn[14:12] == 3'b011 && insn[31:25] == 7'd1 ? INSN_MULHU :
      insn[14:12] == 3'b100 && insn[31:25] == 7'd1 ? INSN_DIV :
      insn[14:12] == 3'b101 && insn[31:25] == 7'd1 ? INSN_DIVU :
      insn[14:12] == 3'b110 && insn[31:25] == 7'd1 ? INSN_REM :
      insn[14:12] == 3'b111 && insn[31:25] == 7'd1 ? INSN_REMU :
      INSN_INVALID) :
    insn_opcode == 7'b11_100_11 && insn[31:7] == 25'd0 ? INSN_ECALL :
    insn_opcode == 7'b00_011_11 ? INSN_FENCE :
    INSN_INVALID; 

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

// addtional stage types for execute, memory, write
typedef struct packed {
    logic [31:0] pc;
    logic [31:0] insn;
    cycle_status_e cycle_status;
    logic [4:0] rs1;
    logic [4:0] rs2;
    logic [4:0] rd;
    logic [11:0] imm_i;
    logic [11:0] imm_s;
    logic [12:0] imm_b;
    logic [20:0] imm_j;
    logic [31:0] imm_i_sext;
    logic [31:0] imm_s_sext;
    logic [31:0] imm_b_sext;
    logic [31:0] imm_j_sext;
    insn_t insn_type;
} stage_execute_t;

typedef struct packed {
    logic [31:0] pc;
    logic [31:0] insn;
    cycle_status_e cycle_status;
    logic [31:0] reg_data;
    logic [4:0] reg_dest;
    logic reg_we;
    logic [31:0] mem_data;
    logic [31:0] mem_addr;
    logic [3:0] mem_we;
    logic halt;
} stage_memory_t;

typedef struct packed {
    logic [31:0] pc;
    logic [31:0] insn;
    cycle_status_e cycle_status;
    logic [31:0] d;
    logic [4:0] rd;
    logic we;
    logic halt;
} stage_write_t;


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
  
  logic branching;
  logic [31:0] branching_to;
  stage_execute_t execute_state;
  stage_memory_t memory_state;
  stage_write_t write_state;

  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (branching) begin
      f_pc_current <= branching_to;
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current + 4;
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
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else if (branching) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_TAKEN_BRANCH
      };
    end else begin
      begin // why the nested begins?? not gonna touch it to be safe
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };
      end
    end
  end

  // get immediates and instruction info
  wire [`OPCODE_SIZE] insn_opcode;
  wire [4:0] insn_rs2, insn_rs1, insn_rd;
  wire [11:0] imm_i, imm_s;
  wire [12:0] imm_b;
  wire [20:0] imm_j;
  wire [31:0] imm_i_sext, imm_s_sext, imm_b_sext, imm_j_sext;
  insn_t insn_type;
  decode_insn dcode(.insn(decode_state.insn),
    .insn_opcode(insn_opcode), .rs2(insn_rs2), .rs1(insn_rs1), .rd(insn_rd),
    .imm_i(imm_i), .imm_s(imm_s), .imm_b(imm_b), .imm_j(imm_j),
    .imm_i_sext(imm_i_sext), .imm_s_sext(imm_s_sext),
    .imm_b_sext(imm_b_sext), .imm_j_sext(imm_j_sext),
    .insn_type(insn_type));

  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  // your code here, though you will also need to modify some of the code above
  // the testbench requires that your register file instance is named `rf`
  
  
  // register file
  logic [31:0] rf_rs1_data, rf_rs2_data, rd_data;
  logic rd_we;
  RegFile rf(.rd(write_state.rd), .rs1(execute_state.rs1), .rs2(execute_state.rs2),
	     .rd_data(rd_data), .clk(clk), .we(rd_we), .rst(rst),
	     .rs1_data(rf_rs1_data), .rs2_data(rf_rs2_data)); 

  // CLA
  logic [31:0] x, y, sum;
  cla adder(.a(x), .b(y), .cin(0), .sum(sum));

  // divider
  logic [31:0] remainder, quotient;
  divider_unsigned_pipelined divider(.clk(clk), .rst(rst), .i_dividend(x), .i_divisor(y),
    .o_remainder(remainder), .o_quotient(quotient));

  /*****************/
  /* EXECUTE STAGE */
  /*****************/
  
  // DFFs for the execute stage of the pipeline
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        rs1: 0,
        rs2: 0,
        rd: 0,
        imm_i: 0,
        imm_s: 0,
        imm_b: 0,
        imm_j: 0,
        imm_i_sext: 0,
        imm_s_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        insn_type: INSN_INVALID
      };
    end else if (branching) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_TAKEN_BRANCH,
        rs1: 0,
        rs2: 0,
        rd: 0,
        imm_i: 0,
        imm_s: 0,
        imm_b: 0,
        imm_j: 0,
        imm_i_sext: 0,
        imm_s_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        insn_type: INSN_INVALID
      };
    end else begin
      execute_state <= '{
        pc: decode_state.pc,
        insn: decode_state.insn,
        cycle_status: decode_state.cycle_status,
        rs1: insn_rs1,
        rs2: insn_rs2,
        rd: insn_rd,
        imm_i: imm_i,
        imm_s: imm_s,
        imm_b: imm_b,
        imm_j: imm_j,
        imm_i_sext: imm_i_sext,
        imm_s_sext: imm_s_sext,
        imm_b_sext: imm_b_sext,
        imm_j_sext: imm_j_sext,
        insn_type: insn_type
      };
    end
  end

  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_1execute ( 
      .insn(execute_state.insn),
      .disasm(x_disasm)
  );

  logic x_halt, reg_we;
  logic [31:0] rs1_data, rs2_data, reg_data, mem_data, mem_addr;
  logic [3:0] mem_we;
  logic [63:0] product;
  
  // determine rs1 and rs2
  always_comb begin

    rs1_data = rf_rs1_data;
    rs2_data = rf_rs2_data;
    
    // WX bypass
    if (write_state.we && write_state.rd == execute_state.rs1 && 
            execute_state.rs1 != 0)
      rs1_data = write_state.d;
    if (write_state.we && write_state.rd == execute_state.rs2 && 
            execute_state.rs2 != 0)
      rs2_data = write_state.d;

    // MX bypass
    if (memory_state.reg_we && memory_state.reg_dest == execute_state.rs1 && 
            execute_state.rs1 != 0)
      rs1_data = memory_state.reg_data;
    if (memory_state.reg_we && memory_state.reg_dest == execute_state.rs2 && 
            execute_state.rs2 != 0)
      rs2_data = memory_state.reg_data;
    
  end

  always_comb begin

    x_halt = 0;
    reg_we = 0;
    reg_data = 0;
    mem_data = 0;
    mem_addr = 0;
    mem_we = 0;

    branching = 0;
    branching_to = 0;

    x = rs1_data;
    y = rs2_data;

    case (execute_state.insn_type)

      INSN_LUI: begin
        reg_we = 1;
        reg_data = {execute_state.insn[31:12], 12'b0};
      end

      INSN_AUIPC: begin
        reg_we = 1;
        reg_data = execute_state.pc + {execute_state.insn[31:12], 12'b0};
      end

      INSN_JAL: begin
        reg_we = 1;
        reg_data = execute_state.pc + 4;
        branching = 1;
        branching_to = execute_state.pc + execute_state.imm_j_sext;
      end

      INSN_JALR: begin
        reg_we = 1;
        reg_data = execute_state.pc + 4;
        branching = 1;
        branching_to = (rs1_data + execute_state.imm_i_sext) & ~32'b1;
      end

      INSN_BEQ: begin
        if (rs1_data == rs2_data) begin
          branching = 1;
          branching_to = execute_state.pc + execute_state.imm_b_sext;
        end
      end

      INSN_BNE: begin
        if (rs1_data != rs2_data) begin
          branching = 1;
          branching_to = execute_state.pc + execute_state.imm_b_sext;
        end
      end

      INSN_BLT: begin
        if ($signed(rs1_data) < $signed(rs2_data)) begin
          branching = 1;
          branching_to = execute_state.pc + execute_state.imm_b_sext;
        end
      end

      INSN_BGE: begin
        if ($signed(rs1_data) >= $signed(rs2_data)) begin
          branching = 1;
          branching_to = execute_state.pc + execute_state.imm_b_sext;
        end
      end

      INSN_BLTU: begin
        if ($unsigned(rs1_data) < $unsigned(rs2_data)) begin
          branching = 1;
          branching_to = execute_state.pc + execute_state.imm_b_sext;
        end
      end

      INSN_BGEU: begin
        if ($unsigned(rs1_data) >= $unsigned(rs2_data)) begin
          branching = 1;
          branching_to = execute_state.pc + execute_state.imm_b_sext;
        end
      end

      INSN_LB: begin

      end

      INSN_LH: begin

      end

      INSN_LW: begin

      end

      INSN_LBU: begin

      end

      INSN_LHU: begin

      end

      INSN_SB: begin

      end

      INSN_SH: begin

      end

      INSN_SW: begin

      end

      INSN_ADDI: begin
        reg_we = 1;
        y = execute_state.imm_i_sext;
        reg_data = sum;
      end

      INSN_SLTI: begin
        reg_we = 1;
        if ($signed(rs1_data) < $signed(execute_state.imm_i_sext))
          reg_data = 1;
        else reg_data = 0;
      end

      INSN_SLTIU: begin
        reg_we = 1;
        reg_data = (rs1_data < execute_state.imm_i_sext) ? 32'b1 : 32'b0;
      end

      INSN_XORI: begin
        reg_we = 1;
        reg_data = rs1_data ^ execute_state.imm_i_sext;
      end

      INSN_ORI: begin
        reg_we = 1;
        reg_data =  rs1_data | execute_state.imm_i_sext;
      end

      INSN_ANDI: begin
        reg_we = 1;
        reg_data = rs1_data & execute_state.imm_i_sext;
      end

      INSN_SLLI: begin
        reg_we = 1;
        reg_data = rs1_data << execute_state.imm_i_sext[4:0];
      end

      INSN_SRLI: begin
        reg_we = 1;
        reg_data = rs1_data >> execute_state.imm_i_sext[4:0];
      end

      INSN_SRAI: begin
        reg_we = 1;
        reg_data = $signed(rs1_data) >>> execute_state.imm_i[4:0];
      end

      INSN_ADD: begin
        reg_we = 1;
        reg_data = sum;
      end

      INSN_SUB: begin
        reg_we = 1;
        y = ~rs2_data + 1'b1;
        reg_data = sum;
      end

      INSN_SLL: begin
        reg_we = 1;
        reg_data = rs1_data << rs2_data[4:0];
      end

      INSN_SLT: begin
        reg_we = 1;
        reg_data = $signed(rs1_data) < $signed(rs2_data) ? 32'b1 : 32'b0;
      end

      INSN_SLTU: begin
        reg_we = 1;
        reg_data = (rs1_data < rs2_data) ? 32'b1 : 32'b0;
      end

      INSN_XOR: begin
        reg_we = 1;
        reg_data = rs1_data ^ rs2_data;
      end

      INSN_SRL: begin
        reg_we = 1;
        reg_data = rs1_data >> rs2_data[4:0];
      end

      INSN_SRA: begin
        reg_we = 1;
        reg_data = $signed(rs1_data) >>> rs2_data[4:0];
      end

      INSN_OR: begin
        reg_we = 1;
        reg_data = rs1_data | rs2_data; 
      end

      INSN_AND: begin
        reg_we = 1;
        reg_data = rs1_data & rs2_data;
      end

      INSN_MUL: begin
        reg_we = 1;
        reg_data = rs1_data * rs2_data;
      end

      INSN_MULH: begin
        reg_we = 1;
        product = { {32{rs1_data[31]}}, rs1_data} * { {32{rs2_data[31]}}, rs2_data};
        reg_data = product[63:32];
      end

      INSN_MULHSU: begin
        reg_we = 1;
        product = { {32{rs1_data[31]}}, rs1_data} * {32'b0, rs2_data};
        reg_data = product[63:32];
      end

      INSN_MULHU: begin
        reg_we = 1;
        product = rs1_data * rs2_data;
        reg_data = product[63:32];
      end

      INSN_DIV: begin
        reg_we = 1;
        if (rs1_data[31]) x = ~rs1_data + 32'b1;
        if (rs2_data[31]) y = ~rs2_data + 32'b1;
        reg_data = rs1_data[31] != rs2_data[31] && rs2_data != 0 ? ~quotient + 32'b1 : quotient;
      end

      INSN_DIVU: begin
        reg_we = 1;
        reg_data = quotient;
      end

      INSN_REM: begin
        reg_we = 1;
        if (rs1_data[31]) x = ~rs1_data + 32'b1;
        if (rs2_data[31]) y = ~rs2_data + 32'b1;
        reg_data = rs1_data[31] ? ~remainder + 32'b1 : remainder;
      end

      INSN_REMU: begin
        reg_we = 1;
        reg_data = remainder;
      end

      INSN_ECALL: begin
        x_halt = 1;
      end

      INSN_FENCE: begin

      end

    endcase

  end

  /****************/
  /* MEMORY STAGE */
  /****************/
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        reg_data: 0,
        reg_dest: 0,
        reg_we: 0,
        mem_data: 0,
        mem_addr: 0,
        mem_we: 0,
        halt: 0
      };
    end else if (branching) begin
      memory_state <= '{
        pc: execute_state.pc,
        insn: execute_state.insn,
        cycle_status: execute_state.cycle_status,
        reg_data: 0,
        reg_dest: 0,
        reg_we: 0,
        mem_data: 0,
        mem_addr: 0,
        mem_we: 0,
        halt: 0
      };
    end else begin 
      memory_state <= '{
        pc: execute_state.pc,
        insn: execute_state.insn,
        cycle_status: execute_state.cycle_status,
        reg_data: reg_data,
        reg_dest: execute_state.rd,
        reg_we: reg_we,
        mem_data: mem_data,
        mem_addr: mem_addr,
        mem_we: mem_we,
        halt: x_halt
      };
    end
  end

  wire [255:0] m_disasm;
  Disasm #(
    .PREFIX("M")
  ) disasm_1memory (
    .insn(memory_state.insn), 
    .disasm(m_disasm)
  );

  assign addr_to_dmem = memory_state.mem_addr;
  assign store_data_to_dmem = memory_state.mem_data;
  assign store_we_to_dmem = memory_state.mem_we;

  /*******************/
  /* WRITEBACK STAGE */
  /*******************/
  always_ff @(posedge clk) begin
    if (rst) begin
      write_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        d: 0,
        rd: 0,
        we: 0,
        halt: 0
      };
    end else begin
      write_state <= '{
        pc: memory_state.pc,
        insn: memory_state.insn,
        cycle_status: memory_state.cycle_status,
        d: memory_state.reg_data,
        rd: memory_state.reg_dest,
        we: memory_state.reg_we,
        halt: memory_state.halt
      };
    end
  end

  wire [255:0] w_disasm;
  Disasm #(
    .PREFIX("W")
  ) disasm_1writeback (
    .insn(write_state.insn),
    .disasm(w_disasm)
  );

  assign trace_writeback_pc = write_state.pc;
  assign trace_writeback_insn = write_state.insn;
  assign trace_writeback_cycle_status = write_state.cycle_status;
    
  always_comb begin
    rd_data = 0;
    rd_we = 0;
    if(write_state.we == 1) begin
      rd_data = write_state.d;
      rd_we = 1;
    end
    halt = write_state.halt;
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
