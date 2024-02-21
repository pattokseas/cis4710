        .section .data
input_string:   .asciz "Hello world!"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string

        # Your code here!
	addi t1, zero, 0x61
	addi t2, zero, 0x7a
	loop:
		lb t3, 0(a0)
		beqz t3, end_program
		bltu t3, t1, end_loop
		bltu t2, t3, end_loop

		addi t3, t3, -32
		sb t3, 0(a0)
		
		end_loop:
		addi a0, a0, 1
		j loop
		
		
        
end_program:
        # jump here when you're done
        j end_program

