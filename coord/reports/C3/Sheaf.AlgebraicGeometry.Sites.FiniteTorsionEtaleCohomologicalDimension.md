## What changed

Proved both clauses of `AlgebraicGeometry.torsionEtaleCohomologicalDimension_finite_of_finiteType`
in the assigned module, with its signature and public imports unchanged. The relative clause
uses a uniform bound on dimensions after arbitrary field extensions. The absolute clause
uses the existing separably closed finite-type cohomology bound and the Ext/derived comparison.

Added `Sheaf.AlgebraicGeometry.Sites.TorsionAbelianDirectImageVanishing`, containing the proved
`AlgebraicGeometry.Etale.isZero_torsion_higherDirectImage_of_forall_field_dimension_le`.
This extends the existing source-library separable-closure descent proof from torsion
coefficient rings to arbitrary torsion abelian sheaves, using ULift Z-module coefficients.
Its two private helpers are proved. Its public imports supply its statement; the source
Kunneth cohomological-dimension module is imported privately for the proof APIs.

The item now imports this helper, `WeilConjectures.AlgebraicGeometry.BaseChangeDimension`,
`WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension`, and
`WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison` for its proof.
Updated `lem-kun-0f10` to this route. Added seven nodes: six attach existing proved source
APIs, and one records the new proved helper. No existing definition or statement changed;
there are no forced adaptations or change records.

Both files compile without warnings using lcompile.py --all (35.7 s and 9.0 s in the final
import check). Checked empty schemes, degree bounds as natural/integer casts, arbitrary
characteristic, and torsion with no common exponent: no additional hypotheses are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.torsionEtaleCohomologicalDimension_finite_of_finiteType`
(node `lem-kun-0f10`). Added 0 holes, split off 0 unproved statements.

The new public theorem
`AlgebraicGeometry.Etale.isZero_torsion_higherDirectImage_of_forall_field_dimension_le`
(node `lem-kun-torsion-abelian-direct-image-dimension-bound`) is proved, as are its private
helpers `torsion_forget_upperStar` and `module_vanishing`. There is no `sorry` in either
delivered Lean module. Existing source-library dependencies are used as given; this does
not claim to close any holes they may transitively use.

## No longer needed

Removed these direct proof imports from the item:

- `WeilConjectures.Mathlib.Topology.KrullDimension`
- `Sheaf.AlgebraicGeometry.EtaleSupport`
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction`
- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
- `WeilConjectures.AlgebraicGeometry.EtaleMayerVietoris`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf`
- `Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound`
- `Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion`
- `Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedPointCohomologicalDimension`
- `WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations`

The original affine support/Mayer–Vietoris induction is unnecessary for this proof. Removed
these direct proof dependencies of `lem-kun-0f10`:

- `def-kun-dimension`
- `def-kun-support`
- `def-weil-finite-type-morphism`
- `lem-kun-affine-direct-image-support-bound`
- `lem-kun-cd-sep-closed-point`
- `lem-kun-cd-stalk-criterion`
- `lem-kun-dimension-formula`
- `lem-sc-affine-noetherian-underlying-space`
- `lem-sc-invert-s-cohomology-induction`
- `lem-weil-pbc-cohomology-over-object-localization`
- `lem-weil-pbc-etale-mayer-vietoris`
- `lem-weil-pbc-etale-mayer-vietoris-pullback`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-higher-direct-image-sheafified-presheaf`
- `lem-weil-pbc-morphism-affine-schemes-affine`
- `lem-weil-pbc-qc-open-immersion-finite-type`
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`
- `lem-weil-pbc-sheafification-exact`
- `lem-weil-pbc-torsion-sheaf-characterizations`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `thm-sc-affine-torsion-cd`

The imports and dependencies above are pruned from this item's direct route, not asserted
to be unused throughout the library. In particular torsion characterizations, stalk
conservativity, and higher-image presheaf descriptions remain below the new source-API
nodes, where the separable-closure proof actually uses them. Dimension and finite-type
notions remain statement dependencies. No Lean module is withdrawn in this delivery.

Withdrew all obsolete top-level `tool_uses` approvals from the item (in original order):

- `lem-kun-cd-sep-closed-point`
- `lem-sc-affine-noetherian-underlying-space`
- `lem-sc-invert-s-cohomology-induction`
- `lem-weil-pbc-cohomology-over-object-localization`
- `lem-weil-pbc-etale-mayer-vietoris`
- `lem-weil-pbc-etale-mayer-vietoris-pullback`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-higher-direct-image-sheafified-presheaf`
- `lem-weil-pbc-qc-open-immersion-finite-type`
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`
- `lem-weil-pbc-sheafification-exact`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `thm-sc-affine-torsion-cd`
- `lem-weil-pbc-morphism-affine-schemes-affine`
- `lem-weil-pbc-torsion-sheaf-characterizations`

These approvals belonged to the replaced proof route. Their withdrawal does not remove
source dependencies of the newly recorded proved APIs.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The source library already has a much shorter uniform
field-extension dimension bound and a separable-closure higher-image argument than the
item's affine support/Mayer–Vietoris plan. The latter source theorem assumes the coefficient
ring is torsion, so it cannot simply be applied with integer coefficients. The new proved
helper instead uses its acyclic-coefficient variant, torsion of each underlying sheaf,
and the exact integer-module/abelian equivalence. This handles arbitrary locally torsion
abelian sheaves, without a uniform exponent or invertibility assumption.

Six source APIs used by this shorter route lacked DAG attachments; the new source nodes
record their actual declarations and proofs. The unit's `realized` statement and steps are
empty; this change is below the unit and does not bypass a realized unit step. The
blueprint update leaves the mathematical statement unchanged.

## New nodes

`lem-kun-uniform-field-extension-dimension-bound`: existing proved
`AlgebraicGeometry.exists_topologicalKrullDim_le_of_isPullback` in
`WeilConjectures.AlgebraicGeometry.BaseChangeDimension`. A finite affine cover and finitely
many algebra generators give a uniform bound after every field extension. No new Lean hole.

`lem-kun-sepclosed-acyclic-module-higher-image-bound`: existing proved
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt_of_acyclic_of_quasiCompact`
in `WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion`. Affine etale
localization reduces higher-image vanishing to the absolute torsion bound, with an
acyclic coefficient forgetful functor. No new Lean hole.

`lem-kun-higher-image-factorization-mono`: existing proved
`AlgebraicGeometry.Etale.mono_higherDirectImageOverMap` in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.TransitionMono`.
An etale surjective base change and a factorization give monicity. No new Lean hole.

`lem-kun-higher-image-mono-limit-vanishing`: existing proved
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isLimit_of_mono` in that same source
module. Continuity of geometric stalks and monic transitions descend vanishing from a
scheme limit. No new Lean hole.

`lem-kun-integer-module-abelian-equivalence`: existing proved
`AlgebraicGeometry.Etale.isEquivalence_sheafCompose_forget₂_uliftInt` in
`WeilConjectures.SixFunctors.BaseChange.DerivedForget`. The equivalence supplies both the
coefficient lift and the exact derived comparison, with objects determined up to the
counit isomorphism used downstream. No new Lean hole.

`lem-kun-algebraic-subextensions-spec-limit`: existing proved
`AlgebraicGeometry.isLimitSubextSpecCone` in
`WeilConjectures.AlgebraicGeometry.FieldExtensionLimit`. Spectra turn the filtered union of
finite subextensions into the required scheme limit. No new Lean hole.

`lem-kun-torsion-abelian-direct-image-dimension-bound`: the new proved helper in
`Sheaf.AlgebraicGeometry.Sites.TorsionAbelianDirectImageVanishing`. It combines the preceding
source APIs, torsion preservation under pullback, and the derived forgetful comparisons.
No work remains on this helper and no unproved split-off is delivered.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
