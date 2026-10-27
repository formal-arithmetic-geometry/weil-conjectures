## What changed

Proved `AlgebraicGeometry.Scheme.DerivedScalarMate.ordinaryTensorIso_existsUnique`
in `Sheaf.Paper.DerivedScalarMateThickLocus`, with its original statement.
The comparison is the tensor braiding followed by the proved normalized
independent-universe scalar-extension comparison, transported to the existing
scalar-extension functor. Private proved helpers check naturality on pure tensors
and establish uniqueness using the sheafification adjunction and sectionwise
tensor extensionality. The coefficient sheaf need not be flat.

Added private proof imports of
`Sheaf.Algebra.Homology.ExtensionTensorComparisonIndependent` and
`Sheaf.SecSmoothPurity.ModuleTensorGenerators`. These supply generic proved
module-sheaf tools, respectively the normalized scalar-extension comparison and
the braiding/map formulas on pure tensors; they do not replace the unit's route.
Updated the item's node, step 1 and its proof dependencies, to record this ordinary
argument while retaining the remaining derived comparison and thick-locus plan.
No public signature, public import, existing definition or other module changed.

Validation: the single-file compiler accepted the proof and import cleanup in
53.3 seconds. `#print axioms ordinaryTensorIso_existsUnique` reported only
`propext`, `Classical.choice`, and `Quot.sound`; the temporary print command was
removed before delivery.

## Proved and sorry left

Closed 1 of the item's 3 holes:
`AlgebraicGeometry.Scheme.DerivedScalarMate.ordinaryTensorIso_existsUnique`.
Added 0 holes and split off 0 statements.

The following 2 existing holes remain unchanged, both attached to
`lem-sfb-derived-scalar-mate-thick-locus`:

- `AlgebraicGeometry.Scheme.DerivedScalarMate.derivedTensorIso_existsUnique`:
  the derived comparison with its representative normalization.
- `AlgebraicGeometry.Scheme.DerivedScalarMate.derivedScalarMateThickLocus`:
  the projection identification, exactness, connecting-arrow compatibility and
  thick isomorphism locus.

## No longer needed

The same-universe dependency `lem-pur-change-of-rings-tensor-comparison`, module
`WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`, is replaced in
this node by the proved independent-universe comparison. Its private import and
obsolete `tool_uses` approval are removed. No declaration or module is withdrawn;
this does not assert that other consumers no longer need that module.

Also removed the unused private imports
`Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, and
`Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`. The first is already
reexported by a public statement dependency; the other three are not used by the
completed ordinary proof. Their nodes remain in the plan for the two unchanged
derived holes; no global pruning claim is made for them.

## Where the brief, the DAG or earlier work was wrong

The ordinary comparison cited in the original step 1 is specialized to coincident
site and coefficient universes. The pro-etale site here has object universe
`u + 1`, morphism universe `u`, and coefficient universe `u + 1`. The existing
independent-universe comparison fits this setting and preserves the full
sectionwise normalization. No statement was disputed or weakened.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
