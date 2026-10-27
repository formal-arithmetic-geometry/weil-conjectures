## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.lisse_tower_connected_etale_presentation`
with a proof assembling connected pointed charts, single-level etale origins, and
pairwise universal reductions of their actual geometric stalks. The existing structure,
theorem signature, and public imports are unchanged. All additional imports are private.

The connected charts are constructed as open connected components of affine
neighborhoods. The point-indexed cover handles an empty base without a choice of point.
Each cohomological interval is transferred directly through the origin's vanishing
property. For a consecutive pair, the existing finite-ring derived local constancy
theorem supplies constant-stalk models on two etale covers. Restricting both models
to their intersection and choosing a member over the point gives a nonempty chart.
The two conditional transports then allow the scalar reduction step there. Choices
are made separately for each pair; no simultaneous markings or cocycle is claimed.

Added `Sheaf.Paper.LisseFiniteQuotientEtaleOrigin`, with one finite-level origin
structure and a remaining descent theorem, and
`Sheaf.Paper.ConstantAdicQuotientModelReduction`, with the remaining scalar comparison
for two supplied constant models on a nonempty chart. Updated the item's DAG proof
to this route. No existing dependency module or shared definition was modified.

Validation: all three files passed remote single-file compilation without warnings.
The final main file took 18.4 seconds; the two helper modules took 21.8 and 11.0 seconds.
Profiling an earlier version isolated 42.6 seconds of serialization cost. Factoring
out the construction on a supplied pointed chart and locally keeping
`constantAdicQuotientRealization` irreducible removed that cost. The local attribute
does not change the exported interface. Profiling options were removed. The theorem
signature was compared textually with the original and is identical. New statements
were checked on empty schemes, empty
charts, zero coefficient rings, zero complexes, and independently varying bounds.
The scalar comparison explicitly requires a point of its chart; removing that
hypothesis would make it false on the empty scheme.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.lisse_tower_connected_etale_presentation`
(node `lem-weil-pbc-lisse-tower-connected-etale-presentation`) by decomposition.
There are zero holes left in the item module. This is not a hole-free proof of the
mathematics: the delivery adds two strictly smaller open statements, so its textual
hole count changes from one to two (one closed, two added).

The two added holes, each the whole proof of a public theorem, are:

- `AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin`
  (`lem-weil-pbc-lisse-finite-quotient-etale-origin`): descent and coefficient transport
  for one fixed finite quotient and an arbitrary bounded complex. It has no AdicTower,
  chosen geometric point, normalization maps, or cover-existence conclusion.
- `AlgebraicGeometry.Scheme.constantAdicQuotient_model_reduction`
  (`lem-weil-pbc-constant-adic-quotient-model-reduction`): universal algebraic reduction
  of two supplied constant models on one nonempty etale chart. It has no boundedness,
  lissity, immersion, Noetherian, etale-descent, or cover-existence hypotheses or claims.

The private `connected_etale_chart`, `restrict_constant_model`, and
`pointed_chart_presentation` helpers prove the connected chart construction,
restriction of constant models along further maps, transfer of cohomological bounds,
pairwise cover intersection, transport of the two models, and assembly of every field
inside the item module. No private lemma
or definition contains a hole. The two remaining statements include full source-based
proofs in their docstrings and matching DAG nodes.

## No longer needed

No original public import is removed, and no existing module or node is withdrawn.
No whole module is claimed pruned. The old whole-diagram normalization-lifting step
is unnecessary: pairwise local constant models and a scalar comparison suffice for
the universal arrows actually requested in the conclusion.

The item's direct proof dependencies now are the two new nodes, the existing
`lem-weil-pbc-finite-ring-derived-local-constancy`, and
`lem-weil-pbc-constant-adic-quotient-scalar-comparison` (its proved completion-quotient
bijection supplies finiteness). The former descent, comparison, tensor, and stalk
nodes remain relevant below the two new nodes or through statement imports; they
are not claimed globally unused. The fixed unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The listed finite-coefficient derived-origin theorem is proved and useful, but its
conclusion is a representative over the original finite ring. It does not directly
supply the inverse-image coefficient identifications, finite local constancy on an
etale chart, or transport in the completion-quotient ring required here. Those are
recorded explicitly in the single-level remaining theorem.

The finite-perfect extraction lemmas use a different completed object, smaller
original coefficients, and perfect models. They cannot be applied to this theorem's
separately bounded AdicTower levels without additional arguments. The existing
finite-ring derived local constancy theorem does apply in the actual coefficient
universe after proving finiteness of the completion quotient. It avoids descending
an entire diagram of normalization arrows. No mathematical statement is disputed.

## New nodes

`lem-weil-pbc-lisse-finite-quotient-etale-origin` records the single finite quotient
descent/transport task, in `Sheaf.Paper.LisseFiniteQuotientEtaleOrigin`. It is strictly
one part of the old argument, independent of towers and normalized stalk arrows.

`lem-weil-pbc-constant-adic-quotient-model-reduction` records consecutive scalar
balancing of already supplied algebraic constant models, in
`Sheaf.Paper.ConstantAdicQuotientModelReduction`. Nonemptiness is supplied explicitly.
It has neither descended etale levels nor a cover or local-constancy assertion.

Both nodes are in `sec-proper-base-change`, unit `sk-thm-properbasechange`, with sources,
complete proof steps, existing declared dependencies, three kinds of Mathlib search,
and verbatim Lean signatures. No change record is necessary: all existing public
interfaces, definitions, instances, attributes, and signatures are preserved.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
