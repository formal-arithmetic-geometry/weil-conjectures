## What changed

In `Sheaf.Paper.DeltaRestriction`, proved the etale restriction identity, the
arbitrary-universe covering criterion, and the normalized pro-etale tensor comparison.
The pro-etale identity is reduced to a separate native closed monoidal restriction
lemma in `Sheaf.AlgebraicGeometry.ProEtaleDerivedRestrictionClosed`. The combining
argument is complete: construct the dual comparison from internal Hom, prove its
evaluation equation, apply the categorical double-dual compatibility identity, and
cancel its inverse for the transported equation. All helper declarations in the item
module are private and proved.

The three existing native tensor and tensor-normalization aliases were
moved verbatim into the new lower module and publicly re-exported by the item. This
shares the exact same native API between the lower theorem and its consumer, avoiding
expensive expanded-instance comparisons. All three qualified names and signatures stay
unchanged. Both `deltaRestrictionPairingBraiding` definitions now directly construct the prescribed
Koszul braiding. Their signatures remain unchanged. This avoids reducing a large
choice predicate. The existing ambient pairing proposition already fixes every
component to this braiding. No target signature or hypothesis changed, no source-library
module changed, and no external forced adaptation was necessary.

## Proved and sorry left

Four original holes are closed in the item module:

- `AlgebraicGeometry.Etale.delta_restriction`: proved from the existing derived closed
  comparison and braided compatibility, with the existing dualizing-object isomorphism.
- `AlgebraicGeometry.Etale.isIso_delta_iff_etale_cover`: proved from restriction and the
  source-library derived-cover detector. A point-indexed subcover handles the arbitrary
  universe of the given cover family.
- `AlgebraicGeometry.ProEtale.deltaRestrictionTensorComparison_normalized`: proved from
  the generic derived tensor comparison and its factorization identities.
- `AlgebraicGeometry.ProEtale.delta_restriction`: complete reduction to the new lower
  theorem, followed by the proved generic categorical comparison.

One hole is added and remains:
`AlgebraicGeometry.ProEtale.exists_normalizedRestrictionMonoidalClosed`, node
`lem-weil-proetale-derived-restriction-closed-monoidal`. This is a theorem about native
slice restriction, with no dualizing object or double-dual map in its statement. Its
normalization fixes its tensor map. The first three closures are proofs; the fourth
is a decomposition. Counts: 4 original holes closed, 1 hole added, 0 holes remaining
in the item module; net 3 holes closed. This does not claim that the pro-etale result
is independent of the new theorem's `sorry`.

## No longer needed

The following private imports were removed from the item module (no declarations or
modules are withdrawn):

- `Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
- `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Mathlib.Algebra.Category.Ring.Limits`
- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `Sheaf.Algebra.Homology.KFlat`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.Compactification.NagataCompactification`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`
- `Sheaf.AlgebraicGeometry.EtaleComparison`
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The proof no longer uses the ringed `SheafOfModules` internal-Hom/evaluation-transpose
bridge: `lem-weil-pbc-ringed-internal-hom-exact-restriction`,
`lem-weil-pbc-ringed-slice-evaluation-transpose`,
`lem-weil-pbc-ringed-pullback-preserves-kflat`, or
`def-weil-pbc-ringed-derived-restriction` as proof dependencies. Its public statement
imports stay intact. The etale model-level Hom-complex calculation is replaced by
proved source-library comparison theorems. The separate lower native pro-etale lemma
retains the localization, exact adjunction, K-injective and K-flat source mathematics
in its own node; those are not claimed globally unnecessary. Imports removed here may
still be reachable elsewhere.

All dependencies removed from the item node's direct proof dependency list are:

- `def-pc-kflat-complex`
- `def-pc-tensor-complex-sheaves`
- `def-pur-hom-complex`
- `def-pur-localized-ringed-site`
- `def-pur-sheaf-tensor-product`
- `def-weil-pbc-derived-categories`
- `def-weil-pbc-proetale-site`
- `def-weil-pbc-ringed-derived-restriction`
- `det-pe-morphisms-etale-comparison`
- `lem-pc-kflat-resolution`
- `lem-pur-kinjective-restrict-localized`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-pbc-ringed-slice-evaluation-transpose`
- `lem-weil-proetale-weakly-etale-localization`
- `prop-pur-kinjective-resolutions-exist`

Some remain statement dependencies or dependencies of the new lower lemma; this list
records direct proof edges removed, not global withdrawals.

The obsolete direct tool-use entries removed from the item's node are:

- `lem-pc-kflat-resolution`
- `lem-pur-kinjective-restrict-localized`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-proetale-weakly-etale-localization`
- `prop-pur-kinjective-resolutions-exist`
- `det-pe-morphisms-etale-comparison`

These are removals of obsolete direct approvals, not withdrawals of the underlying
nodes. Some remain dependencies of the new native lemma or of existing source proofs.
The blueprint unit has no realized statement or proof-step attachments, so its route
is not bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing ringed-site restriction lemmas use variable-ring `SheafOfModules`, while
the item's conclusions use native `Sheaf J (ModuleCat Λ)`. They cannot be applied by
unification alone. The etale source library already supplies the native closed
comparison, so that branch needs no new bridge. The pro-etale source library supplies
underived closed restriction and a derived tensor comparison, but not their combined
normalized derived closed monoidal structure; the new node states precisely that
missing lower result.

The source covering detector accepts a cover indexed in the scheme universe, whereas
the item's cover index is in an arbitrary universe. Choosing a covering member above
each point resolves this without restricting the statement. Empty schemes and empty
cover families are included. The closed comparison has no perfectness or boundedness
condition; zero objects, the identity restriction, and arbitrary unbounded complexes
are covered by the slice/K-injective argument in the new docstring. The prescribed
braiding is constructed directly instead of extracted through its componentwise
normalization predicate; this changes its implementation, not the Koszul components.

## New nodes

`lem-weil-proetale-derived-restriction-closed-monoidal` states the independent native
closed monoidal restriction result, sourced to Stacks 08JB and the derived Koszul
tensor construction. Its proof plan includes the normalization uniqueness argument
and identification of the closed comparison by evaluation; it is strictly below the
original double-dual assertion. LeanSearch, LeanFinder, Loogle and source grep, together with the inspected native source
results are recorded in its node. The new module contains this one public theorem, the three moved native API
declarations, and one `sorry`.

Change records: `coord/changes/B9-delta-restriction-native-braiding.md` and
`coord/changes/B9-delta-restriction-native-api.md`.

Validation: the new lower module and the assigned module compile without warnings;
the assigned module took 36.9 seconds. The first delivery preflight requested a separate
LeanSearch entry (LeanFinder and Loogle count as one search kind); the actual search
and node entry have now been added. Its additional axiom probe timed out and the tool
said it will rerun that probe at merge.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
