/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned_pipelined (
    input wire clk, rst,
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
    
    // stage 1

    wire [31:0] stage1_dividend;
    wire [31:0] stage1_remainder;
    wire [31:0] stage1_quotient;

    stage stage1(
        .i_dividend(i_dividend),
        .i_divisor(i_divisor),
        .i_remainder(32'b0),
        .i_quotient(32'b0),
        .o_dividend(stage1_dividend),
        .o_remainder(stage1_remainder),
        .o_quotient(stage1_quotient)
    );
    
    // registers between stages

    logic [31:0] reg_dividend;
    logic [31:0] reg_divisor;
    logic [31:0] reg_remainder;
    logic [31:0] reg_quotient;

    always_ff @(posedge clk) begin
        if(rst) begin
            reg_dividend <= 32'b0;
            reg_divisor <= 32'b0;
            reg_remainder <= 32'b0;
            reg_quotient <= 32'b0;
        end else begin
            reg_dividend <= stage1_dividend;
            reg_divisor <= i_divisor;
            reg_remainder <= stage1_remainder;
            reg_quotient <= stage1_quotient;
        end
    end

    // stage 2

    wire [31:0] stage2_dividend;
    wire [31:0] stage2_remainder;
    wire [31:0] stage2_quotient;

    stage stage2(
        .i_dividend(reg_dividend),
        .i_divisor(reg_divisor),
        .i_remainder(reg_remainder),
        .i_quotient(reg_quotient),
        .o_dividend(stage2_dividend),
        .o_remainder(stage2_remainder),
        .o_quotient(stage2_quotient)
    );

    assign o_remainder = stage2_remainder;
    assign o_quotient = stage2_quotient;

endmodule

module stage (
    input wire [31:0] i_dividend,
    input wire [31:0] i_divisor,
    input wire [31:0] i_remainder,
    input wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    wire [31:0] dividends[17];
    wire [31:0] remainders[17];
    wire [31:0] quotients[17];
    
    assign dividends[0] = i_dividend;
    assign remainders[0] = i_remainder;
    assign quotients[0] = i_quotient;

    genvar i;
    for(i = 1; i < 17; i = i + 1) begin
        divu_1iter iter(
            .i_dividend(dividends[i - 1]),
            .i_divisor(i_divisor),
            .i_remainder(remainders[i - 1]),
            .i_quotient(quotients[i - 1]),
            .o_dividend(dividends[i]),
            .o_remainder(remainders[i]),
            .o_quotient(quotients[i])
        );
    end

    assign o_dividend = dividends[16];
    assign o_remainder = remainders[16];
    assign o_quotient = quotients[16];

endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

  // copy your code from HW2A here
  wire [31:0] remainder = (i_remainder << 1) | ((i_dividend >> 31) & 32'b1);
  wire lt = remainder < i_divisor;

  assign o_remainder = lt ? remainder : remainder - i_divisor;
  assign o_quotient = lt ? i_quotient << 1 : (i_quotient << 1) | 32'b1;
  assign o_dividend = i_dividend << 1;

endmodule
