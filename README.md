This is a LLVM 3.4 pass that uses switch statements to implement a  
proof of concept for the the accelerated array optimization for  
Symbolic Execution. The original idea for the optimization was  
to implement it by instrumenting the target program before  
running it through symbolic execution. This prototype showed  
promise and drastically improved the performance of symbolic 
execution on many programs. However, due to some of the overhead
of instrumentation we found that implementing the optimization
directly in the Symbolic Executin engine would be optimal.

You can find a version of KLEE (Symbolic Execution Engine) that
employs this optimization along with its ISSTA '17 publication
at: www.srg.doc.ic.ac.uk/projects/klee-array

Example Optimization:
// Consider the array: 
int array[5] = {0,2,4,6,8};

// With a symbolic index read (index is computed during runtime):
val = array[symb_idx];

// This creates issues during symbolic execution due to the 
// complicated nature of generally modeling arrays in an SMT Logic.
// Since statically allocated arrays have known values this 
// encoding is overly complex. Therefore, we replace the above 
// symbolic index read with a set of instructions:
switch (symb_idx)
{
	case 0:
		val = 0;
		break;
	case 1:
		val = 2;
		break;
	case 2:
		val = 4;
		break;
	case 3:
		val = 6;
		break;
	case 4:
		val = 8;
		break;
}
