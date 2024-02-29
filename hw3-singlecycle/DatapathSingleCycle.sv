`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`include "../hw2a/divider_unsigned.sv"
`include "../hw2b/cla.sv"

module negative(input wire [31:0] in, output wire [31:0] out);
    assign out = ~in + 1;
endmodule

module sub(input wire [31:0] x, y, output wire [31:0] out);
    wire [31:0] minus_y;
    negative neg(.in(y), .out(minus_y));
    cla add(.a(x), .b(minus_y), .cin(0), .sum(out));
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

    assign regs[0] = 32'd0;	 // zero always zero

    assign rs1_data = regs[rs1]; // read registers
    assign rs2_data = regs[rs2];
    
    genvar i;
    for(i = 1; i < NumRegs; i = i + 1) begin  // make DFFs for R1-R31
        always_ff @(posedge clk) begin
            if(rst) regs[i] <= 32'b0; 		       // reset
	    else if(we && rd == i) regs[i] <= rd_data; // write
        end
    end

endmodule

module DatapathSingleCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output logic [`REG_SIZE] addr_to_dmem,
    input logic [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem
);

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

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

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  `include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end


  // set up register file
  logic [31:0] rd_data, rs1_data, rs2_data;
  logic reg_we;
  RegFile rf(.rd(insn_rd), .rs1(insn_rs1), .rs2(insn_rs2), 
	     .rd_data(rd_data), .clk(clk), .we(reg_we), .rst(rst),
	     .rs1_data(rs1_data), .rs2_data(rs2_data));
  
  // set up CLA
  logic [31:0] x, y, sum;
  cla adder(.a(x), .b(y), .cin(0), .sum(sum));

  // set up divider
  logic [31:0] remainder, quotient;
  divider_unsigned divider(.i_dividend(x), .i_divisor(y),
    .o_remainder(remainder), .o_quotient(quotient));
  
  logic [63:0] product;
  logic [31:0] load, addr;

  logic illegal_insn;

  always_comb begin
    illegal_insn = 1'b0;

    halt = 1'b0;
    pcNext = pcCurrent + 4;

    reg_we = 1'b0;
    rd_data = 32'b0;
    x = 32'b0;
    y = 32'b0;

    product = 64'b0;

    load = 32'b0;
    addr = 32'b0;

    addr_to_dmem = 32'b0;
    store_data_to_dmem = 32'b0;
    store_we_to_dmem = 4'b0;

    case (insn_opcode)
      OpLui: begin
        reg_we = 1'b1;
	      rd_data = { insn_from_imem[31:12], 12'b0 };
      end
      OpAuipc: begin
        reg_we = 1'b1;
        rd_data = pcCurrent + { insn_from_imem[31:12], 12'b0 };
      end
      OpRegImm: begin
        reg_we = 1;
        x = rs1_data;
        y = imm_i_sext;
        if (insn_addi)  rd_data = sum;
        else if (insn_slti)  rd_data = ($signed(rs1_data) < $signed(imm_i_sext)) ? 32'b1 : 32'b0;
	      else if (insn_sltiu) rd_data = (rs1_data < imm_i_sext) ? 32'b1 : 32'b0;
        else if (insn_xori)  rd_data = rs1_data ^ imm_i_sext;
	      else if (insn_ori)   rd_data = rs1_data | imm_i_sext; 
        else if (insn_andi)  rd_data = rs1_data & imm_i_sext;
        else if (insn_slli)  rd_data = rs1_data << imm_i_sext[4:0];
        else if (insn_srli)  rd_data = rs1_data >> imm_i_sext[4:0];
        else if (insn_srai)  rd_data = $signed(rs1_data) >>> imm_i[4:0];
        else illegal_insn = 1'b1;
      end
      OpRegReg: begin
        reg_we = 1;
        x = rs1_data;
        y = rs2_data;
        if      (insn_add)  rd_data = sum;
        else if (insn_sub)  begin 
		      y = ~rs2_data + 1'b1; 
		      rd_data = sum;
	        end
        else if (insn_sll)    rd_data = rs1_data << rs2_data[4:0];
	      else if (insn_slt)    rd_data = $signed(rs1_data) < $signed(rs2_data) ? 32'b1 : 32'b0;
	      else if (insn_sltu)   rd_data = (rs1_data < rs2_data) ? 32'b1 : 32'b0;
	      else if (insn_xor)    rd_data = rs1_data ^ rs2_data;
	      else if (insn_srl)    rd_data = rs1_data >> rs2_data[4:0];
        else if (insn_sra)    rd_data = $signed(rs1_data) >>> rs2_data[4:0];
	      else if (insn_or)     rd_data = rs1_data | rs2_data;
	      else if (insn_and)    rd_data = rs1_data & rs2_data;
        else if (insn_mul)    rd_data = rs1_data * rs2_data;
        else if (insn_mulh)   begin
          product = { {32{rs1_data[31]}}, rs1_data} * { {32{rs2_data[31]}}, rs2_data};
          rd_data = product[63:32];
          end
        else if (insn_mulhsu) begin
          product = { {32{rs1_data[31]}}, rs1_data} * {32'b0, rs2_data};
          rd_data = product[63:32];
          end
        else if (insn_mulhu)  begin
          product = rs1_data * rs2_data;
          rd_data = product[63:32];    
          end
        else if (insn_div)    begin
            if (rs1_data[31]) x = ~rs1_data + 32'b1;
            if (rs2_data[31]) y = ~rs2_data + 32'b1;
            rd_data = rs1_data[31] != rs2_data[31] && rs2_data != 0 ? ~quotient + 32'b1 : quotient;
          end
        else if (insn_divu)   rd_data = quotient;
        else if (insn_rem)    begin
            if (rs1_data[31]) x = ~rs1_data + 32'b1;
            if (rs2_data[31]) y = ~rs2_data + 32'b1;
            rd_data = rs1_data[31] ? ~remainder + 32'b1 : remainder;
          end
        else if (insn_remu)   rd_data = remainder;
        else illegal_insn = 1'b1;
      end
      OpLoad: begin 
        reg_we = 1'b1;
        addr_to_dmem =rs1_data + imm_i_sext;
        case(addr_to_dmem[1:0])
            2'b00: load = load_data_from_dmem;
            2'b01: load = { 8'b0, load_data_from_dmem[31:8] };
            2'b10: load = { 16'b0, load_data_from_dmem[31:16] };
            2'b11: load = { 24'b0, load_data_from_dmem[31:24] };
        endcase
        if      (insn_lb)  rd_data = { {24{load[7]}}, load[7:0]};
        else if (insn_lh)  rd_data = { {16{load[15]}}, load[15:0]};
        else if (insn_lw)  rd_data = load;
        else if (insn_lbu) rd_data = { 24'b0, load[7:0] };
        else if (insn_lhu) rd_data = { 16'b0, load[15:0] };
        else illegal_insn = 1'b1;  
        addr_to_dmem &= ~32'b11; 
      end
      OpStore: begin  
        addr_to_dmem = rs1_data + imm_s_sext;
        if      (insn_sb) store_we_to_dmem = 4'b0001;
        else if (insn_sh) store_we_to_dmem = 4'b0011;
        else if (insn_sw) store_we_to_dmem = 4'b1111;
        else illegal_insn = 1'b1;
        store_data_to_dmem = rs2_data << addr_to_dmem[1:0] * 8;
        store_we_to_dmem <<= addr_to_dmem[1:0]; 
        addr_to_dmem &= ~32'b11; 
      end
      OpJal: begin
        reg_we = 1'b1;
        rd_data = pcCurrent + 4;
        pcNext = pcCurrent + imm_j_sext;
      end
      OpJalr: begin
        reg_we = 1'b1;
        rd_data = pcCurrent + 4;
        pcNext = (rs1_data + imm_i_sext) & ~32'b1;
      end
      OpBranch: begin
          if((insn_beq && rs1_data == rs2_data) ||
	           (insn_bne && rs1_data != rs2_data) ||
             (insn_blt && $signed(rs1_data) < $signed(rs2_data)) ||
	           (insn_bge && $signed(rs1_data) >= $signed(rs2_data)) ||
             (insn_bltu && rs1_data < rs2_data) ||
	           (insn_bgeu && rs1_data >= rs2_data)) 
                pcNext = pcCurrent + imm_b_sext; 
      end
      OpEnviron: begin
        halt = 1; 
      end
      OpMiscMem: begin

      end
      default: begin
        illegal_insn = 1'b1;
      end
    endcase
  end

endmodule

/* A memory module that supports 1-cycle reads and writes, with one read-only port
 * and one read+write port.
 */
module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

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

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
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

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathSingleCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule
