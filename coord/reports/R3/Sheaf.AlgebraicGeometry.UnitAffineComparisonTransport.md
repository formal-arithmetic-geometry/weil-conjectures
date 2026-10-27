## What changed

Constructed `unitAffineSymmetry` in `UnitAffineComparisonTransportCore`: normalize the
pulled-back structural units, transport cohomology along inverse pullback symmetry,
and undo normalization. Proved its scalar equation `unitAffineSymmetry_smul` using
cohomology pullback semilinearity and the pullback projection identity. This construction
is explicit; no arbitrary witness is chosen from an unproved existence theorem.

`unitAffineComparison` composes this additive isomorphism with the given linear
equivalence and `unitAffineSectionsEquiv`; `unitAffineComparisonFamily` assembles the
explicit pointwise maps. `exists_unitAffineComparisonTransport` packages this family. Its scalar proof is complete. The restriction square for this exact
construction is isolated in `UnitAffineComparisonTransportNaturality`, with its proof
plan and source. The existing theorem's signature and public imports are unchanged.
No source-library module is modified. The existing node records the reduction.

## Proved and sorry left

This is a decomposition, not a net hole closure: one upper hole is replaced by one
strictly smaller restriction-square obligation. The item has zero remaining `sorry`s;
the delivered modules together have one.

Closed upper hole: `AlgebraicGeometry.Scheme.Modules.exists_unitAffineComparisonTransport`
(node `new-unit-affine-comparison-transport`). The additive equivalence construction,
its invertibility, `unitAffineSymmetry_smul`, `unitAffineComparison_smul`, and the
private `unitAffineComparisonFamily_scalar` are proved without new holes.
`unitAffineSectionsEquiv` is the identity identification of evaluation with global
sections; `unitAffineSectionsEquiv_smul` proves its scalar equation. These avoid
unfolding the evaluation construction inside the large cohomology goal.

Added and remaining hole:
`AlgebraicGeometry.Scheme.Modules.unitAffineComparison_canonical_naturality`
(node `new-unit-affine-comparison-canonical-naturality`). This fixes the comparison
explicitly and asks only for its restriction equation; neither an existential witness
nor scalar compatibility remains in its conclusion.

## No longer needed

No original import is removed and no module is withdrawn. The original node's direct
proof dependencies are replaced by the proved construction and its naturality step.
The structural-unit isomorphism and cohomology functoriality/linearity remain needed
through the construction and naturality node.

`lem-sc-etale-tensor-unit-restriction-equation`
(`WeilConjectures.AlgebraicGeometry.EtaleTensorUnitRestrictionEquation`) is not used:
it treats unit sections, whereas the remaining square needs compatibility of the
coefficient morphisms before taking cohomology.

`def-weil-pbc-tensor-pullback-ordinary-comparison`
(`Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`) is not used: the construction
uses the actual tensor structural-unit adjoint map. The remaining naturality plan uses
uniqueness of the normalized adjunction to compare its composition maps directly.
These declarations are preserved and may still have other consumers; no global pruning
of their modules is claimed.

## Where the brief, the DAG or earlier work was wrong

The naturality step needs an explicit bridge between the section-normalized composition
in the coherent edge and the mate-normalized composition in the etale restriction.
The original listed section restriction result alone does not supply that cohomology
square. Establishing this bridge remains the named naturality obligation. No statement
or existing definition is changed, and the unit route is preserved.

## New nodes

`new-unit-affine-symmetry` records the explicit structural-unit cohomology isomorphism
and its proved scalar equation, in `UnitAffineComparisonTransportCore`. Its helper
maps, functoriality, identity equations and module instances are attached to this node.

`new-unit-affine-comparison-canonical-naturality` records the single remaining
restriction square in `UnitAffineComparisonTransportNaturality`. Its source and proof
in words describe normalization, adjunction uniqueness, cohomology functoriality and
pullback projection equations. Identity arrows, empty schemes and zero modules require
no extra hypotheses; the statement is about the explicit constructed family.

Validation: all three delivered modules compile, taking 27.3, 14.4 and 17.0 seconds.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
