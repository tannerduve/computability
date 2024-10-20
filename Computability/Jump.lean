import Computability.TuringDegrees

/- To Do:
1. Define jump operator on partial functions, and lift it to Turing degrees
2. Show that for all f, f strictly reduces to its jump
3. Show that the jump operator is monotone ie. if f ≤ᵀ g then f' ≤ᵀ g'

This is an encoding problem. The jump of a partial recursive
function f is the function f' defined as follows:

f(e) = 1 if the eᵗʰ partial function recursive in f halts on e, and is undefined otherwise.
That is, f' is the halting problem for f. 

To enumerate partial functions we need a natural number encoding of them.
-/