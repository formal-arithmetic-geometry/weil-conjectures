## What changed

Proved `AlgebraicGeometry.Scheme.adicFiniteGradedLayer_triangle` in
`Sheaf.Paper.AdicCoefficientFiltration`, preserving its statement, the four public
constructions, and every existing public import. Added only proved private helpers
and private proof imports. Updated the item's node proof and dependencies to record
the actual argument.

The proof constructs the algebraic kernel short exact sequence, realizes it exactly
as constant module sheaves, and tensors its degree-zero distinguished triangle.
It proves the constant regular-module comparisons from locally bijective
sheafification units. Existing K-flat single-tensor and ordinary extension-tensor
comparisons identify the endpoints; `adicFiniteRho` identifies the iterated reduction.
An explicit triangle isomorphism transports all three arrows, including the boundary.
The natural extension-tensor comparison is reused through `import all` from
`ConstantCompletionEquivalence`; it is a proved private helper, not a new assumption.

Source checked: Stacks `proetale.tex`, lemma-compare-truncations-constructible (09BR),
first displayed triangle; `sites-cohomology.tex`, definition-derived-tor (06YU)
and lemma-derived-base-change (06YY); current blueprint integral-models unit.
The argument works for zero rings, J=0, J=top and the empty scheme and assumes no
flatness of the quotient, no boundedness and no constructibility.

Validation: the final server single-file compilation passed without warnings in
11.9 s. Delivery preflight provides its independent compile/axiom checks. The added single-tensor proof import passes import-direction
checking. No shared definition or interface changes, hence no consumer adaptations.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.adicFiniteGradedLayer_triangle`
(node `lem-sfb-adic-coefficient-filtration-triangle`).

Zero `sorry` remain in the item; zero holes added; zero statements split off.
All private helpers are fully proved. Existing dependency theorems are reused as
per the stage-3 contract; no additional unresolved theorem is introduced.

## No longer needed

None. No original imports removed, no modules or DAG nodes withdrawn. The source
kernel-sequence/tensor/balancing route is realized, and all four original proof
dependencies remain used through the published interfaces. The node additionally
records the existing K-flat resolution, single-tensor, ordinary extension-tensor,
and tensor-presentation comparisons actually used. No new node is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The DAG's endpoint-balancing step required
explicit constant-module and tensor-unit identifications; these are now proved
private helpers rather than another restatement of the filtration obligation.
The unit's statement and route are preserved. No second reader was started, as
specified by the dispatcher brief; the delivery receives the maintainer's independent
review.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
