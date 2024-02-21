/* Matthew Pattok (mpattok) */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    logic [31:0] dividend;
    logic [31:0] remainder;
    logic [31:0] quotient;

    // logic [31:0] d_tmp;
    // logic [31:0] r_tmp;
    // logic [31:0] q_tmp;
    logic [31:0] i = 32'b0;
	
    always @(i) begin
            logic [31:0] d_tmp;
    logic [31:0] r_tmp;
    logic [31:0] q_tmp;
	    divu_1iter iter(.i_dividend(dividend),
		    .i_divisor(i_divisor),
		    .i_remainder(remainder),
		    .i_quotient(quotient),
		    .o_dividend(d_tmp),
		    .o_remainder(r_tmp),
		    .o_quotient(q_tmp)
	    );
	    dividend = d_tmp;
	    remainder = r_tmp;
	    quotient = q_tmp;
	    i = i + 1;
        end
    end

    assign o_remainder = remainder;
    assign o_quotient = quotient;

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

    wire [31:0] rem_tmp;
    wire [31:0] q_tmp;
    
    assign rem_tmp = (i_remainder << 1) | ((i_dividend >> 31) & 32'h00000001);
    assign q_tmp = i_quotient << 1;
    
    wire lt = rem_tmp < i_divisor;
    // wire [31:0] gte;
    // for(i = 1; i < 32; i = i + 1) assign gte[i] = 1'b0;
    // assign gte[0]  = ~lt;
        
    // assign o_remainder = rem_tmp - i_divisor * gte;
    // assign o_quotient = q_tmp | gte;
    //
    assign o_remainder = lt ? rem_tmp : rem_tmp - i_divisor;
    assign o_quotient = lt ? q_tmp : q_tmp | 32'h00000001;
    assign o_dividend = i_dividend << 1;


endmodule
