## What changed

Filled all four theorem proofs in `Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality`.
The public signatures, public imports, coefficient objects, derived tensor and braiding
are unchanged. Added only proof imports and a proved private dualizability-test helper.

Strong braided pullback uses the existing explicit ordinary module tensorator, its
braiding law, preservation of flat modules and the generic left-derived monoidal API.
Dual preservation maps the evaluation/coevaluation pairing. Scalar compatibility is
whiskering of `condensedPointModuleDerivedComparison` by the fixed realization on the point.

For locality the private helper constructs one morphism from a K-flat resolution and
`DerivedCategory.DualizabilityDatum`. Weakly etale inverse image has an exact left adjoint:
abelian left Kan extension over lifts, sheafification, module linearization using the
projection formula, and coefficient transport. The existing native internal-Hom comparison
and generic `DualizabilityDatum.isDualizable_Q_obj_map_iff` show that the same morphism
tests dualizability after restriction. Cover conservativity finishes the converse.
This reuses the source-library chain-level argument, without changing that source tree.
Updated the item's DAG proof and dependencies to this route.
Local tensor-colimit/coherence instances are cached to avoid repeated expensive
elaboration of the balanced module tensor; all mathematical constructions are unchanged.

The proof uses the existing `lem-proetale-pullback-internal-hom` as a tool for ordinary
internal modules, plus `new-proetale-inverse-image-module-flat`,
`new-integral-residue-ordinary-monoidal`, `new-integral-residue-ordinary-braiding`,
`def-sfb-modobj-linearization-transport-adjunction` and
`lem-weil-pbc-localization-kan-discrete-lifts`. They are actual existing constructions;
the unit's old sectionwise route would require transporting both monoidal presentations.
No new maintainer tool approvals were inserted.

## Proved and sorry left

Closed 4 original holes, by declaration:

- `AlgebraicGeometry.ProEtale.condensed_derivedPullback_exact_symmetricMonoidal`.
- `AlgebraicGeometry.ProEtale.condensed_derivedPullback_preserves_dualizable`.
- `AlgebraicGeometry.ProEtale.condensed_scalarRealization_pullback`.
- `AlgebraicGeometry.ProEtale.condensed_dualizable_iff_proetale_cover`.

All realize `lem-zl-condensed-lisse-proetale-locality`. Zero holes remain in this module;
zero holes added; zero statements split off. The private helper
`condensed_dualizability_test` is proved. Existing dependencies may retain their own
holes; this delivery does not claim to close those.

Validation: the final module compiles through `lcompile.py` in 55.1 seconds,
with no errors or warnings. All five public declaration signatures and public imports
match the original file. The updated proof dependency list equals the union of the
proof-step uses, and the new imports introduce no cycle.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`.
- `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`.
- `Sheaf.CategoryTheory.DualizableJointlyConservativeLocality`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

The planned sectionwise derived tensor/coherence/closed route is replaced by the native
internal-module monoidal and chain-level dualizability APIs. Therefore these planned
proof dependency nodes are not needed by this argument:

- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-sfb-ringed-derived-monoidal-comparisons`.
- `lem-sf-ringed-derived-closed-symmetric-monoidal`.
- `lem-zl-proetale-coefficient-slice-closed-comparison`.
- `lem-zl-dualizable-jointly-conservative-locality`.

Also removed obsolete tool-use entries for the first three above and
`lem-weil-pbc-ringed-internal-hom-exact-restriction`,
`lem-weil-pbc-ringed-slice-evaluation-transpose`, and
`lem-sfb-proetale-object-inverse-image-restriction`.

Only `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction` and
`Sheaf.CategoryTheory.DualizableJointlyConservativeLocality` leave this item's transitive
Lean import closure. Other consumers retain them; no module leaves the current
`TargetsCheck` import closure. No files or declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statements are unchanged and no source assertion is disputed. The DAG's sectionwise
closed-comparison assembly did not directly match the public internal-module presentation.
The existing native ordinary Hom theorem and generic chain-level criterion give a shorter
route and avoid constructing that comparison of presentations.

The proof keeps arbitrary scheme morphisms in the monoidal and scalar clauses. It uses
weak etaleness only for the cover criterion. No boundedness, finite generation,
quasi-compactness or restriction on the cover's index universe was added. Empty and infinite
covers and the zero coefficient ring remain included. The blueprint unit route is unchanged.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
