`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

// N must be some 2^k where k >= 1
module gpN #(parameter N = 2)
    (input wire [N-1:0] gin, pin, input wire cin,
    output wire gout, pout, output wire [N-2:0] cout);
    
    // base case	
    if(N == 2) begin : base_case // idk what label is for, compiler told me to
        assign gout = gin[1] | pin[1] & gin[0];  // G = G1 + P1*G0
	assign pout = pin[1] & pin[0];		 // P = P1 * P0
	assign cout[0] = gin[0] | pin[0] & cin;  // C = G + P*C0
    end else begin : recursive_case // same for this label
	// figure out the first half
        wire low_gout, low_pout; wire [N/2-2:0] low_cout; 
	gpN #(.N(N/2)) low(.gin(gin[N/2-1:0]), .pin(pin[N/2-1:0]),
		           .cin(cin),
			   .gout(low_gout), .pout(low_pout), .cout(low_cout));
        // figure out the second half
	wire low_carry = low_gout | low_pout & cin;
	wire hi_gout, hi_pout; wire [N/2-2:0] hi_cout;
	gpN #(.N(N/2)) hi(.gin(gin[N-1:N/2]), .pin(pin[N-1:N/2]),
		          .cin(low_carry),
			  .gout(hi_gout), .pout(hi_pout), .cout(hi_cout));
        // combine them
        assign gout = hi_gout | hi_pout & low_gout;
	assign pout = hi_pout & low_pout;
	assign cout = {hi_cout, low_carry, low_cout};
    end

endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */

module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   // TODO: your code here
    // can just use gpN
    gpN #(.N(4)) gp(.gin(gin), .pin(pin), .cin(cin),
	            .gout(gout), .pout(pout), .cout(cout));
endmodule




/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here
    // can just use gpN
    gpN #(.N(8)) gp(.gin(gin), .pin(pin), .cin(cin),
	            .gout(gout), .pout(pout), .cout(cout));

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

    // TODO: your code here
    // get gin and pin
    wire [31:0] g = a & b;
    wire [31:0] p = a ^ b;
    // figure out generation & propagation
    wire gen, prop; wire [30:0] carry;
    gpN #(.N(32)) gp(.gin(g), .pin(p), .cin(cin),
	            .gout(gen), .pout(prop), .cout(carry)); 
    // S = P XOR C
    assign sum = p ^ {carry, cin};

endmodule
