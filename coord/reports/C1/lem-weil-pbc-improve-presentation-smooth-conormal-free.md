# Stage 1 delivery: `lem-weil-pbc-improve-presentation-smooth-conormal-free`

## Worker report

Split the smooth case of Stacks Smoothing Ring Maps 07CE into the initial
smooth presentation, the symmetric-algebra construction, and the free
conormal calculation. Added one unsplit projective-symmetric-algebra
conormal node. No Lean attachment or WANTED source.

## Review by C1

I read `literature/stacks-project/smoothing.tex` at Lemma 07CE and its proof
(lines 357-414), and the smooth conormal splitting used in Lemma 07CH.
The item's conclusion is the smooth case at a=1: a retraction through
Sym_A(I/I²), smooth over A, with an R-polynomial presentation whose
conormal module is free. The new child states only the conormal calculation
for this polynomial presentation under the explicit hypothesis that
M=I/I² is projective. It is unsplit, has no proof steps, introduces all its
rings and maps, and records LeanSearch, Loogle, and Mathlib source searches.
I searched current DAG nodes by 07CE, symmetric conormal, and 07EV. The
existing 07EV node records that its unrestricted conormal assertion is
false; the new child's projectivity hypothesis is used to split q and is
therefore essential.

Step 1 takes a finite presentation from smoothness, uses the cited smooth
conormal-splitting node at a=1 to make M finite projective, and explicitly
splits the surjection A^m to M into K plus M. Step 2 uses the symmetric
algebra's universal property for the degree-zero retraction, its
finite-projective smoothness node, and its finite-presentation node for the
surjection Q to C. Step 3 applies the child's split conormal sequence and
the already constructed K⊕M=A^m, giving J/J²=C^m. I checked the statement
of each cited node against that use. The source's right-exact sequence
alone would not give the left injection; the child isolates precisely this
additional argument. For M=0 the construction reduces to C=A and the
sequence to K⊗A, consistent with the claim; a=1 makes localization trivial.

The worker made the projectivity requirement explicit and did not repeat
the false general 07EV assertion. `review_split.py` passes; `check_dag.py`
finds no cycles and only unrelated reachability warnings. No further
correction was needed after this review.
