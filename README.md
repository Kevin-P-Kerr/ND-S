# ND-S: A Non-Deterministic Scheme Interpeter #

## What It Is ##
ND-S is a Scheme interpreter that supports chronological backtracking through a special form called amb. For example, we can open the REPL and type the following:

		ND-S => (amb 1 2 3)
		1
		ND-S => try-again
		2
		ND-S => try-again
		3
		ND-S => try-again
		There are no more values
		ND-S => try-again
		There is no problem

We can also define a procedure (require p) as follows

	ND-S => (define (require p) (if (not p) (amb) (quote OK)))

Which allows us to write stuff such as this

	ND-S => (define x (amb 1 2 9 10)) (require (> x 5)) (+ x 1)
	10
	ND-S => try-again
	11
	
 
## Brief Q&A ##

*How does it work?*

During the evaluation process, the interpter passes around two continuations, one to execute upon success, another to execute if a failure is raised.  Failurs are raised if amb is called with no arguments, or try-again is typed in the top level repl.  For a detailed discussion of Scheme and non-determinism, see SICP chapter 4.3, from which this interpreter is derived.  A link can be found here: mitpress.mit.edu/sicp/full-text/sicp/book/node88.html.

*Why are there two versions?*

 ND-S was originally written in Python; however, due to the recursive nature of the interpterter, it will quickly cause Python to either reach it's recursion limit or segfault.  The Javascript version performs a little better, but still runs into its recursion limit fairly quickly.

*Is this a complete implementation of Scheme?*

No.  As of this writing, cons, car, cdr, and null? remain to be implemented, as well as let expressions.  These will hopefully be forthcoming.
