# Stage 1 delivery: `lem-weil-pbc-separable-residue-cotangent-injective`

## Worker report

Split the cotangent-injectivity assertion into five steps following Stacks
Algebra 00TU. No new nodes, Lean attachments, or WANTED sources.

## Review by C1

I read `literature/stacks-project/algebra.tex` at Lemma 00TU and its proof
(lines 38702-38737), together with its cited differential-comparison 02HQ
and split-conormal 02HP statements. The item retains 00TU's finitely
generated separable residue-field hypothesis. The existing separable-field
definition makes the finitely generated extension separably generated, as
used in step 2. I checked the statements of the differential-comparison,
primitive-element, and square-zero-section nodes against each application.

Step 1 quotients by m² and uses the 02HQ node at n=1 to preserve the target
map. Step 2 chooses a finite separating transcendence basis; finite
generation then makes the remaining separable algebraic extension finite,
and the primitive-element leaf supplies y with P'(y) nonzero. Step 3 lifts
the rational-function subfield because every nonzero polynomial evaluation
has nonzero residue and hence is a unit in the local square-zero ring.
Step 4 adjusts an arbitrary lift of y by -P(y)/P'(y); the square-zero
polynomial expansion makes it an exact root and yields a residue-map
section. Step 5 applies the split-conormal node to that section and carries
the injection back through step 1's isomorphism. The case of a zero
maximal ideal gives a zero source map; an empty transcendence basis is
handled by the same primitive-element step. No uncited source assertion is
used in the proof.

The worker made the lift and adjustment explicit. `review_split.py` passes;
`check_dag.py` finds no cycles and only unrelated reachability warnings. I
requested no further correction.
