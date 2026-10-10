# Stage 1 delivery: `lem-weil-pbc-finite-over-nagata-nagata`

## Worker report

Split the finite case of Stacks Algebra 032T in four steps, expanding the
finite-domain argument of 032I. No new node, Lean attachment, or WANTED source.
The quotient R/I is the final special case.

## Review by C1

I read `literature/stacks-project/algebra.tex` at Lemma 032T (lines
45700-45717) and the finite case of Lemma 032I (lines 45224-45231). The item
requires a finite ring map from a Nagata ring and concludes that its target
and each quotient R/I are Nagata. This is the finite specialization of 032T;
the cited 032I assumes a Noetherian N-2 domain, precisely what the prime
quotients of a Nagata ring supply. I checked the statements of the finite
algebra Noetherian, finite-dimensional domain is field, finite algebra
integral, integral transitivity, and field-degree nodes against each use.

Step 1 contracts an arbitrary prime q and makes B=S/q finite over the domain
A=R/p; the quotient is injective by the definition of p, while finite
algebras over Noetherian rings are Noetherian. Step 2 localizes B at the
nonzero elements of A. It remains a nonzero domain, finite-dimensional over
Frac(A), so the cited field lemma identifies it with Frac(B); the field-degree
node then makes any finite extension of Frac(B) finite over Frac(A). Step 3
uses N-2 for A and integral transitivity for finite B/A to identify the two
integral closures in that extension. A finite A-generating set also generates
over B, proving B is N-2. Step 4 applies the result to the finite quotient
R/I. The zero ring causes no missing prime case, and the field argument starts
only after taking a prime quotient, so its domains are nonzero. No new node
or route outside the unit is introduced. `review_split.py` passes and
`check_dag.py` has no cycles, only unrelated reachability warnings. I
requested no correction after this review.
