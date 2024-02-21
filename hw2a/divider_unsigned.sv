/* Matthew Pattok (mpattok) */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
    
    // wires we need: initial values + 32 outputs
    wire [31:0] remainders[33];
    wire [31:0] quotients[33];
    wire [31:0] dividends[33];

    // assign initial values
    assign remainders[0] = 32'b0;
    assign quotients[0] = 32'b0;
    assign dividends[0] = i_dividend;

    // run the loop, assigning output for i-1 to values for i
    genvar i;
    for(i = 1; i < 33; i = i + 1) begin
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

    assign o_remainder = remainders[32];
    assign o_quotient = quotients[32];

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
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    wire [31:0] remainder = (i_remainder << 1) | ((i_dividend >> 31) & 32'b1);
    wire lt = remainder < i_divisor;

    assign o_remainder = lt ? remainder : remainder - i_divisor;
    assign o_quotient = lt ? i_quotient << 1 : (i_quotient << 1) | 32'b1;
    assign o_dividend = i_dividend << 1;

endmodule
