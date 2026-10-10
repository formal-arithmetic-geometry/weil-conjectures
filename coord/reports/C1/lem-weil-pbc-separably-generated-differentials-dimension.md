# Stage 1 delivery: `lem-weil-pbc-separably-generated-differentials-dimension`

## Worker report

Split the differential-basis calculation from Stacks Algebra 031W into four
steps, and added a Mathlib leaf for differential base change across a
finite separable field extension. No Lean attachment or WANTED source.

## Review by C1

I read `literature/stacks-project/algebra.tex` at the proof of 031W
(lines 44189-44202), which states the finite-separable differential
calculation with its computation omitted, and the dimension assertion in
00TV. I checked 00RX and 00RT for the polynomial basis and localization.
The item states exactly the basis and dimension conclusion for the given
separating transcendence basis. The new child states only the canonical
differential map for finite separable F⊆K, with the base field k and all
module structures introduced; it has no proof steps while a leaf. I searched
the current DAG by separable differentials and 031W and found no duplicate.

I read pinned Mathlib v4.33.1 `RingTheory/Etale/Kaehler.lean` at lines
38-50 and `Etale/Field.lean` at line 98. With (R,S,T)=(k,F,K),
`Algebra.FormallyEtale.of_isSeparable` supplies the instance from K/F,
and `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` is the
canonical K-linear isomorphism stated in the child. Its application lemma
matches a tensor of a differential with the differential after inclusion.
The child's match records those files and lines, and its LeanSearch,
LeanFinder/Loogle, and source search were checked.

Step 1 identifies F with the fraction field of k[X] using algebraic
independence. Step 2 applies the cited polynomial-differential-basis and
localization nodes, preserving each basis vector. Step 3 proves K/F finite
from the finite set of field generators, then applies the checked Mathlib
leaf; no separability is silently inferred from algebraicity alone.
Step 4 transports the r-element basis and uses the transcendence-degree
definition. When r=0 the free module and dimension are zero, consistent
with finite separable algebraic K/k. `review_split.py` passes and
`check_dag.py` has no cycles, only unrelated reachability warnings. No
further correction was needed.
