## What changed

Filled `AlgebraicGeometry.Scheme.completedKoszulTensorConeComparison` without changing
its statement or its original public import. The proof constructs the source and quotient
tensor comparisons, verifies their strict successor naturality, and transports the existing
natural signed tensor-cone isomorphism along the resulting square. The auxiliary sequence
comparisons take arbitrary object sequences and transition maps before specialization, to
avoid repeatedly unfolding the completed coefficient constructions. The constructor from
successor-compatible component isomorphisms is also checked over an arbitrary category;
the private component isomorphism definitions are irreducible with explicit naturality lemmas.

Added `Sheaf.Paper.CompletedKoszulTensorConeComparisonAux`, which contains the generic
levelwise mapping-cone transport, strict successor tower comparison, and arbitrary-category
tower isomorphism constructor used by the target proof.

Added `Sheaf.Paper.CompletedKoszulTensorAugmentationComponent`, proving the fixed-level
normalization square by total tensor summands. Its proof needs only the two unit equations
and the nonzero-exterior-summand equation for the map at P; it needs no naturality of those
two maps and no cone or tower assertion.

Added `Sheaf.Paper.CompletedKoszulUnitZeroIso`, proving invertibility of the actual recorded
completed Koszul unit. The proof constructs the constant rank-one unit inverse, uses the
exterior degree-zero equivalence and the existing proved scalar-extension unit comparison,
and verifies the recorded tensor normalization using the scalar-extension morphism formula.
No existing module besides the assigned item was changed; the auxiliary module is new and
proof-only imported by the assigned item.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.completedKoszulTensorConeComparison`
(1 of 1 original holes).

Additional proved declarations:
- `AlgebraicGeometry.Scheme.completedKoszulTensorAugmentationComponent`
  (`lem-weil-pbc-completed-koszul-tensor-augmentation-component`).
- `AlgebraicGeometry.Scheme.completedKoszulUnitZero_isIso`
  (`lem-weil-pbc-completed-koszul-unit-zero-iso`).

There are zero `sorry` occurrences in the delivered Lean files, and zero new holes.
No obligation is split off with a postponed proof. Existing imported proof obligations
elsewhere in the library are unchanged.

## No longer needed

Removed the redundant private import of
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle` from the main module; the new
component statement publicly imports this API because its signature uses the single comparison.

No module is withdrawn. The existing public import of
`Sheaf.Paper.CompletedKoszulCoefficientConeRealization` remains necessary for the published
cochain tensor instances, and transitively exposes the original statement definitions.
The proof does not use the coefficient-cone realization theorem, the existence or uniqueness
theorems for the completed tensor augmentation, or the pro-zero assertion of
`flatConstantTensorProZeroCones`. These modules remain for the definitions they supply;
this delivery does not claim their removal from the targets' import closure.

The original proof dependency on the augmentation-existence theorem is replaced by the new
proved component normalization lemma. Reconstruction definitions, the tensor-instance
module and the signed tensor-cone lemma remain dependencies. No unit-level statement or
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan's degree-zero unit-invertibility claim is correct, but there was no public theorem
for the actual normalized completed unit. Existing private lemmas in `KoszulQuotientLimit`
and `CompletedAdicKoszulKFlat` concern the uncompleted constant unit. The new proved unit
lemma supplies the missing interface and checks its specified section formula.

The vanishing of the coefficient map outside degree zero follows from its target being a
single complex; the nonzero-summand hypothesis is needed only for the map at P. Naturality
in P is also unnecessary for the fixed-level normalization argument. The original theorem
and all its hypotheses are preserved.

## New nodes

`lem-weil-pbc-completed-koszul-tower-cone-transport`: generic levelwise cone and strict tower transport;
its node is `dag/nodes/sec-proper-base-change/lem-weil-pbc-completed-koszul-tower-cone-transport.json`.

`lem-weil-pbc-completed-koszul-tensor-augmentation-component`: the fixed-level equality of
two maps of complexes, strictly before the strict tower and cone arguments. Its proof is
complete in `Sheaf.Paper.CompletedKoszulTensorAugmentationComponent`.

`lem-weil-pbc-completed-koszul-unit-zero-iso`: invertibility of the recorded degree-zero
completed Koszul unit, including its scalar-tensor normalization. Its proof is complete in
`Sheaf.Paper.CompletedKoszulUnitZeroIso`.

The change record is `coord/changes/completed-koszul-tensor-cone-comparison.md`.

The assigned node's proof, proof dependencies and proof origin were updated to the actual
argument. No change record is needed: no existing statement, definition, attribute or public
import was changed.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
