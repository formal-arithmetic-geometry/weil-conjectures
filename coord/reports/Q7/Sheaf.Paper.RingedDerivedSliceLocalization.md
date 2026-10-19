## What changed

Retained the interrupted attempt's extraction of the unchanged interfaces into
Sheaf.Paper.RingedDerivedSliceData and its complete proofs of
RingedSliceAdjunctionSquare.ofMate, ringedSliceLocalizationModel and the parent
ringedDerivedSliceLocalization assembly. The parent constructs the localization
isomorphism from the derived counit and the ordinary localization isomorphism;
naturality gives the generator equation.

Completed the direct-image comparison construction in
Sheaf.Paper.RingedSliceDerivedComparisons. A proved private generic lemma applies
the K-injective derivability criterion to both composites and uses
Functor.rightDerivedUnique. Its factorization equation proves normalization on
all complexes. Restriction preserves K-injectives by
isKInjective_restrict_localized. The inverse-mate assertion is separate in Sheaf.Paper.RingedSliceDerivedMate,
where its full proof is now written. The derived-image construction is also proved.

All six delivery modules compile in dependency order. Caching the restriction,
localization and ordinary adjunction functors and the four sheaf-composition
instances reduces the mate module's artifact-producing compile to 40.4 seconds.
The parent compiles in 43.8 seconds. The preceding full appended mate axiom/sorry
probe passed in 45.2 seconds (SHEAF-PROBED 1), reporting no unexpected axioms and
no direct sorry. The final dry run passed compilation, all appended axiom/sorry probes and server
preflight (commit f31f5952be; review class CODEX). All six modules have zero
textual sorries. The route records follow these proofs.

The public interfaces extracted from the original module are unchanged. All
proof imports are non-public. No other group's held module is adapted.

## Proved and sorry left

Original item holes: 1, SheafOfModules.ringedDerivedSliceLocalization.
The parent has a complete assembly proof. No split-off sorry remains in the sandbox.
Closed holes: one. Added holes: zero.

Complete proofs written:

- SheafOfModules.RingedSliceAdjunctionSquare.ofMate, by Mathlib mate identities.
- SheafOfModules.ringedSliceLocalizationModel, from the localization telescope.
- SheafOfModules.ringedSliceDerivedImage_exists, by resolving-class left derivation,
  K-injective right derivation and Mathlib's derived adjunction.
- SheafOfModules.ringedSliceDerivedMate_isIso, by the normalized mate identity on
  flat-term K-flat representatives and naturality along a resolution isomorphism.
- SheafOfModules.ringedSliceDerivedComparisons, by right-derived uniqueness and
  inverse-mate invertibility.
- SheafOfModules.ringedDerivedSliceLocalization, from those results.

Holes added: zero. Every delivered definition and helper has a complete proof body.

## No longer needed

These original direct imports now belong to the publicly reexported data module,
where the unchanged definitions and statements need them:

- Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
- Mathlib.CategoryTheory.Adjunction.Additive
- Mathlib.CategoryTheory.Functor.Derived.LeftDerived
- Mathlib.CategoryTheory.Functor.Derived.RightDerived
- Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose
- Sheaf.CategoryTheory.LocalCoefficientLocalization
- Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
- Sheaf.CategoryTheory.RingedSectionLocalizationRing
- Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

The parent assembly no longer directly imports these original proof modules:

- Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd
- Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro
- Sheaf.CategoryTheory.KInjectiveTotalDerived
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
- Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
- Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
- Sheaf.CategoryTheory.RingedToposMorphism
- Sheaf.CategoryTheory.SiteCoveringAxioms
- Sheaf.Paper.KFlatRingedToposPullback
- Sheaf.Paper.ProjectionMateExact
- Sheaf.Paper.RingedTopoiDerivedPullback
- Sheaf.Paper.SliceSiteLocalization
- WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

These are removals from the parent, not claims that whole modules leave the
final target closure. KInjectiveRestrictLocalized is now used explicitly by the
comparison proof. Resolution ingredients remain where the completed derived constructions need them.

ProjectionMateExact (lem-weil-pbc-ringed-projection-mate-exact) is unnecessary
for the categorical coherence: Mathlib's mateEquiv_counit_symm and
unit_mateEquiv_symm supply it. The precoverage SliceSiteLocalization interface
is unnecessary here: LocalizeRingedSiteMorphismGeneral supplies the ordinary
Grothendieck-topology localization. The comparison proof no longer needs a
fraction construction for beta, K-flat descent, or a separately chosen
K-injective Hom model. The mate proof also avoids fraction-level Hom calculations: the unit identity
and naturality suffice. Its actual imports instead provide K-flat resolutions,
restriction of K-flatness, the equivalence of K-flat predicates and restriction
of flat modules.
The derived-image plan now uses the proved continuous ringed-topos presentation
and supplied K-flat pullback theorem. Its former direct dependencies on
lem-weil-pbc-ringed-topoi-derived-pullback and
lem-weil-pbc-ringed-topoi-module-adjunction are replaced by that shorter route;
those results can remain transitive dependencies of the supplied theorem.
The obsolete explicit public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
is also removed; the new theorem uses the defining exactness predicate instead.
The parent does not use lem-weil-pbc-ringed-localization-rhom-calculus or its
module Sheaf.Paper.RingedLocalizationRHomCalculus: only the extracted
RingedLocalizationModels calculations are needed. Its unused proof dependency is removed.
No entire module is claimed pruned from the target closure. The unit's own route remains untouched.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt overlooked the already proved
continuousRingedToposModuleDirectImage_exists presentation theorem. Together
with RingedToposMorphism.exists_kFlatPullback and uniqueness of left adjoints,
it gives preservation of quasi-isomorphisms between flat-term K-flat complexes
by the canonical site pullback. Resolving-class essential constancy and the
K-injective good-object criterion provide the two composition universal properties
required by Mathlib Adjunction.derived. Its unit factorization proves normalization. The unused exploratory
helper and its imports are omitted from the delivery.

The interrupted mate attempt used a whole-natural-transformation identity rewrite
that forced Lean to unfold the sheaf pushforward construction. Mapping the ordinary
comparison square to complexes and checking its identity componentwise avoids that
cost. Generic unit-normalization and isomorphism-transport lemmas handle the two
remaining categorical calculations with complete private proofs. Local aliases for
the restriction functors, their comparison isomorphisms and Q prevent repeated
instance searches when applying those categorical lemmas. The earlier dry run's
mate axiom-probe timeout is resolved by this change; the full probe now passes.

The current source tree has moved the specialized flatness definition from
Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat to the source library, while some
compiled dependencies still import its previous owner. The new derived-image
existence theorem states termwise flatness by its defining predicate: exactness of
tensoring on the right for the canonical monoidal structure. This is definitionally
the same condition, introduces no new definition and avoids importing the obsolete
module or a duplicate declaration. Its remaining proof uses the existing flatness API.

The earlier combined comparison proof was too large a remaining obligation:
its right-derived comparison can be constructed directly by the existing
K-injective derivability structure. This part is now proved. An invertible
right-adjoint comparison need not have invertible mate, so that assertion is
proved explicitly and is not inferred from beta's invertibility alone.

Edge cases: empty sites and zero rings require no exclusions. Localization
at zero or a nilpotent section is the zero localization and is still flat.
Identity site maps recover the identity mate. No signature of a target was
changed; the parent only renames its unused continuity binder hc to _hc.

## New nodes

- def-weil-pbc-ringed-slice-derived-data: extracted existing interfaces and the
  proved generic mate construction.
- lem-weil-pbc-ringed-slice-derived-image-exists: proved global total derived
  adjunction existence and normalization, without slice or localization claims.
- lem-weil-pbc-ringed-slice-derived-comparisons: the derived direct-image
  comparison, now proved from K-injective derivability and the proved mate theorem.
- lem-weil-pbc-ringed-slice-derived-mate-isIso: only inverse-mate invertibility
  for an already supplied and normalized beta. Its proof computes on flat-term K-flat representatives and extends by
  naturality along resolution isomorphisms.
- lem-weil-pbc-ringed-slice-localization-model: proved ordinary localization
  isomorphism normalized on the unit.

Change record: coord/changes/ringed-derived-slice-data.md.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
