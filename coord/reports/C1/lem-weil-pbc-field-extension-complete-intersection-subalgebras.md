# Stage 1 delivery: `lem-weil-pbc-field-extension-complete-intersection-subalgebras`

## Worker report

Split the existing statement into five steps following Stacks Algebra 07BV and
the localization presentation of 00SA. No new node, Lean attachment, or WANTED
source. The proof constructs a complete-intersection subalgebra around every
finite subset of the field, then shows these subalgebras are directed.

## Review by C1

I read `literature/stacks-project/algebra.tex` at the proof of Lemma 07BV
(lines 44527-44559) and the localization presentation in Lemma 00SA (lines
35868-35881). The item's field-extension and explicit regular-sequence
conclusion match the first assertion of 07BV. No separability hypothesis is
used; that hypothesis belongs only to its second assertion. I read the cited
finite-transcendence-basis and complete-intersection-model node statements:
the former supplies a finite basis of k(E), and the latter supplies a domain
model with fraction field k(E), not just an abstract complete intersection.

Step 1 applies those basis definitions to finite E. Step 2 takes exactly the
regular sequence and injective domain model stated by the model node. Step 3
uses the principal-localization definition: the product of finitely many
nonzero denominators remains nonzero in the domain and makes every element
of E lie in A_g. Step 4 uses the polynomial-ring and regular-sequence
definitions to verify the presentation A_g = k[X,T]/(f,hT-1); coefficientwise
injectivity preserves the earlier equations, and hT-1 is a nonzerodivisor in
the domain A[T]. Step 5 is the elementary directedness argument: the union of
two finite generating sets lies in one more algebra constructed by steps 1-4.
The empty E case uses g=1; the zero-denominator and zero-quotient cases are
excluded by A being a domain and embedding into k(E). The worker chose the
explicit presentation because the existing dimension-based localization
node does not state the regular-sequence presentation this item needs.

No new node requires a duplicate or Mathlib search. `review_split.py` passes;
`check_dag.py` has no cycles and only unrelated reachability warnings. I
requested no correction after this review.
