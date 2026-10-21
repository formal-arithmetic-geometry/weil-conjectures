/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Sheaf.CategoryTheory.RingedPresentationData
public import Sheaf.CategoryTheory.RingedCoefficientCounitPresentations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.GeometricModuleTransport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Canonical unbounded derived comparisons on sheaf slices

Source: Stacks Project, Modules on Sites, Tag 04IF; Sites, Tag 04H1;
Cohomology on Sites, Tags 0G7E, 08FI, 07A6 and 07A7
(blueprint: lem-sbc-ringed-topos-sheaf-slice-derived-comparison).

## Main definitions and statement

* `SheafSliceSetLocalization`: the sectionwise normalization of slice localization.
* `RingedSheafSliceOrdinaryComparison`: the canonical ordinary ringed square.
* `HasRingedSheafSliceDerivedComparison`: the derived comparisons and their normalizations.
* `ringedSheafSliceDerivedComparison`: existence for every ringed morphism and target sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory

/-- The canonical element restriction commutes with forgetting the module structure.
Source: Stacks 04IE, sectionwise restriction
(blueprint: lem-sbc-ringed-topos-sheaf-slice-derived-comparison). -/
def sheafSliceUnderlyingRestriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    elementModulePullback.{u, u} (localCoefficientRings R) A ⋙
        underlying (presentationElementRing R A) ≅
      underlying R ⋙ elementSheafPullback A :=
  Iso.refl _

/-- The canonical localization identification, fixed on every section of every fibre.
The projection from `A × F` is the second projection, since `Over.star A` uses the first
projection as its structure map. Source: Stacks 0791, 04H1 and 04IF
(blueprint: lem-sbc-ringed-topos-sheaf-slice-derived-comparison). -/
structure SheafSliceSetLocalization
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A : Sheaf J (Type u)}
    (S : RingedSheafSliceAdjunctionData R A) where
  iso : Over.star A ⋙ S.fibreEquivalence.inverse ≅ elementSheafPullback A
  sections : ∀ (F : Sheaf J (Type u)) (U : Cᵒᵖ) (s : A.obj.obj U)
    (x : (S.fibreEquivalence.inverse.obj ((Over.star A).obj F)).obj.obj
      (elementObj A U s)),
    (iso.hom.app F).hom.app (elementObj A U s) x =
      (prod.snd : A ⨯ F ⟶ F).hom.app U
        (((S.fibre_iso.hom.app ((Over.star A).obj F)).app (elementObj A U s) x).val)

/-- The canonical ordinary ringed square, exact restrictions and resolution preservation.

This is output data, not an assumption on the ringed morphism. Ordinary pullbacks are
specified as left adjoints to the supplied induced module direct images; this determines
them with their adjunctions up to the unique adjunction-preserving isomorphism. The ordinary
comparison is fixed as the mate of the geometric direct-image identification. The derived
output proposition below uses this ordinary output as its parameter.

Source: Stacks 04IF, 04H1, 0G7E, 08FI, 07A6, 07A7 and 09T5
(blueprint: lem-sbc-ringed-topos-sheaf-slice-derived-comparison). -/
structure RingedSheafSliceOrdinaryComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u)) where
  sourceSlice : RingedSheafSliceAdjunctionData (localCoefficientRings RX) (f.inverse.obj A)
  targetSlice : RingedSheafSliceAdjunctionData (localCoefficientRings RY) A
  sourceLocalization : SheafSliceSetLocalization sourceSlice
  targetLocalization : SheafSliceSetLocalization targetSlice
  slice : RingedToposMorphism
    (localCoefficientRings (presentationElementRing RX (f.inverse.obj A)))
    (localCoefficientRings (presentationElementRing RY A))
  sliceInverse : slice.inverse ≅ targetSlice.fibreEquivalence.functor ⋙
    Over.post f.inverse ⋙ sourceSlice.fibreEquivalence.inverse
  starComparison : Over.star A ⋙ Over.post f.inverse ≅
    f.inverse ⋙ Over.star (f.inverse.obj A)
  starComparison_formula : ∀ F : Sheaf K (Type u),
    (starComparison.hom.app F).left = prodComparison f.inverse A F
  sets : elementSheafPullback A ⋙ slice.inverse ≅
    f.inverse ⋙ elementSheafPullback (f.inverse.obj A)
  sets_formula : ∀ F : Sheaf K (Type u), sets.hom.app F =
    slice.inverse.map (targetLocalization.iso.inv.app F) ≫
      sliceInverse.hom.app (targetSlice.fibreEquivalence.inverse.obj ((Over.star A).obj F)) ≫
      sourceSlice.fibreEquivalence.inverse.map ((Over.post f.inverse).map
        (targetSlice.fibreEquivalence.counitIso.hom.app ((Over.star A).obj F))) ≫
      sourceSlice.fibreEquivalence.inverse.map (starComparison.hom.app F) ≫
      sourceLocalization.iso.hom.app (f.inverse.obj F)
  structural : sets.hom.app ((sheafCompose K (forget RingCat)).obj
      (localCoefficientRings RY)) ≫
      (elementSheafPullback (f.inverse.obj A)).map f.ringMap = slice.ringMap
  pullback : modules RY ⥤ modules RX
  [pullbackAdditive : pullback.Additive]
  ordinaryAdjunction : pullback ⊣ f.modules
  slicePullback : ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A) ⥤
    ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A))
  [slicePullbackAdditive : slicePullback.Additive]
  sliceOrdinaryAdjunction : slicePullback ⊣ slice.modules
  sigma : elementModulePullback.{u, u} (localCoefficientRings RY) A ⋙ slicePullback ≅
    pullback ⋙ elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)
  delta : f.modules ⋙ elementModulePullback.{u, u} (localCoefficientRings RY) A ≅
    elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A) ⋙ slice.modules
  ordinary_mate :
    (mateEquiv ordinaryAdjunction sliceOrdinaryAdjunction
      (TwoSquare.mk _ _ _ _ sigma.hom)).natTrans = delta.hom
  delta_underlying : ∀ E : modules RX,
    (underlying (presentationElementRing RY A)).map (delta.hom.app E) ≫
      slice.underlying.hom.app
        ((elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).obj E) =
    (sheafSliceUnderlyingRestriction RY A).hom.app (f.modules.obj E) ≫
      (elementSheafPullback A).map (f.underlying.hom.app E) ≫
      (mateEquiv f.adj slice.adj (TwoSquare.mk _ _ _ _ sets.hom)).natTrans.app
        ((underlying RX).obj E) ≫
      slice.direct.map ((sheafSliceUnderlyingRestriction RX (f.inverse.obj A)).inv.app E)
  [targetRestrictionAdditive :
    (elementModulePullback.{u, u} (localCoefficientRings RY) A).Additive]
  [sourceRestrictionAdditive :
    (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).Additive]
  [targetRestrictionLimits :
    PreservesFiniteLimits (elementModulePullback.{u, u} (localCoefficientRings RY) A)]
  [sourceRestrictionLimits :
    PreservesFiniteLimits
      (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A))]
  [targetRestrictionColimits :
    PreservesFiniteColimits (elementModulePullback.{u, u} (localCoefficientRings RY) A)]
  [sourceRestrictionColimits :
    PreservesFiniteColimits
      (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A))]
  targetKFlat : ∀ T : CochainComplex (modules RY) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := RY) T →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := RY) (T.X n)) →
    CochainComplex.IsKFlatIndependentCoefficients (R := presentationElementRing RY A)
        ((onComplex (elementModulePullback.{u, u} (localCoefficientRings RY) A)).obj T) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := presentationElementRing RY A)
        (((onComplex (elementModulePullback.{u, u} (localCoefficientRings RY) A)).obj T).X n)
  sourceKInjective : ∀ I : CochainComplex (modules RX) ℤ, I.IsKInjective →
    CochainComplex.IsKInjective ((onComplex
      (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A))).obj I)
attribute [instance] RingedSheafSliceOrdinaryComparison.pullbackAdditive
  RingedSheafSliceOrdinaryComparison.slicePullbackAdditive

/-- The derived part of the canonical sheaf-slice square, on its ordinary output data.
All comparisons use actual exact derived restrictions and the existing normalized derived
adjunction interface. Source: Stacks 04IF, 0G7E, 08FI, 07A6, 07A7 and 09T5
(blueprint: lem-sbc-ringed-topos-sheaf-slice-derived-comparison). -/
def HasRingedSheafSliceDerivedComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {RX : Sheaf J CommRingCat.{u}} {RY : Sheaf K CommRingCat.{u}}
    {f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY)}
    {A : Sheaf K (Type u)}
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A)))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A))]
    (o : RingedSheafSliceOrdinaryComparison RX RY f A) : Prop :=
  letI := o.targetRestrictionAdditive
  letI := o.sourceRestrictionAdditive
  letI := o.targetRestrictionLimits
  letI := o.sourceRestrictionLimits
  letI := o.targetRestrictionColimits
  letI := o.sourceRestrictionColimits
  ∃ globalDerived : DerivedAdjunction.{w} o.pullback f.modules o.ordinaryAdjunction,
  ∃ sliceDerived : DerivedAdjunction.{w} o.slicePullback o.slice.modules o.sliceOrdinaryAdjunction,
  ∃ theta : (elementModulePullback.{u, u} (localCoefficientRings RY) A).mapDerivedCategory.{w, w} ⋙
      sliceDerived.left ≅
    globalDerived.left ⋙
      (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategory.{w, w},
  ∃ beta : globalDerived.right ⋙
      (elementModulePullback.{u, u} (localCoefficientRings RY) A).mapDerivedCategory ≅
    (elementModulePullback.{u, u}
      (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategory.{w, w} ⋙
      sliceDerived.right,
  -- globalFlat_computation
  (∀ T : CochainComplex (modules RY) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := RY) T →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := RY) (T.X n)) →
      IsIso (globalDerived.epsilon.app T)) ∧
  -- sliceFlat_computation
  (∀ T : CochainComplex (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := presentationElementRing RY A) T →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u}
      (R := presentationElementRing RY A) (T.X n)) →
      IsIso (sliceDerived.epsilon.app T)) ∧
  -- theta_representative
  (∀ T : CochainComplex (modules RY) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := RY) T →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := RY) (T.X n)) →
    theta.hom.app (DerivedCategory.Q.{w}.obj T) ≫
      (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategory.{w, w}.map
        (globalDerived.epsilon.app T) ≫
      (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategoryFactors.{w, w}.hom.app
        ((onComplex o.pullback).obj T) =
    sliceDerived.left.map
      ((elementModulePullback.{u, u}
        (localCoefficientRings RY) A).mapDerivedCategoryFactors.{w, w}.hom.app T) ≫
      sliceDerived.epsilon.app
        ((onComplex (elementModulePullback.{u, u} (localCoefficientRings RY) A)).obj T) ≫
      DerivedCategory.Q.{w}.map ((NatIso.mapHomologicalComplex o.sigma (.up ℤ)).hom.app T)) ∧
  -- beta_representative
  (∀ I : CochainComplex (modules RX) ℤ, I.IsKInjective →
    (elementModulePullback.{u, u} (localCoefficientRings RY) A).mapDerivedCategory.{w, w}.map
        (globalDerived.eta.app I) ≫
      beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
      sliceDerived.right.map ((elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategoryFactors.{w, w}.hom.app I) =
    (elementModulePullback.{u, u}
      (localCoefficientRings RY) A).mapDerivedCategoryFactors.{w, w}.hom.app
        ((onComplex f.modules).obj I) ≫
      DerivedCategory.Q.{w}.map ((NatIso.mapHomologicalComplex o.delta (.up ℤ)).hom.app I) ≫
      sliceDerived.eta.app ((onComplex (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A))).obj I)) ∧
  -- derived_mate
  ((mateEquiv globalDerived.adj sliceDerived.adj
      (TwoSquare.mk _ _ _ _ theta.hom)).natTrans = beta.hom) ∧
  -- counit
  (∀ E : DerivedCategory (modules RX),
    theta.hom.app (globalDerived.right.obj E) ≫
      (elementModulePullback.{u, u}
        (localCoefficientRings RX) (f.inverse.obj A)).mapDerivedCategory.{w, w}.map
        (globalDerived.adj.counit.app E) =
    sliceDerived.left.map (beta.hom.app E) ≫ sliceDerived.adj.counit.app
      ((elementModulePullback.{u, u} (localCoefficientRings RX)
        (f.inverse.obj A)).mapDerivedCategory.{w, w}.obj E))

/-- Every ringed-topos morphism has canonical ordinary and unbounded derived comparisons
on the slice at any sheaf of sets.

Source: Stacks 04IF and 04H1; unbounded computations: 0G7E, 08FI, 07A6, 07A7 and 09T5
(blueprint: lem-sbc-ringed-topos-sheaf-slice-derived-comparison).

Proof.
1. Use `ringed_sheaf_slice_adjunction` for the small element-site presentations. The arrowwise
   functor `Over.post f.inverse` is left exact and its right adjoint sends `H → f⁻¹A` to
   `A ×_{f_*f⁻¹A} f_*H`, using the original unit; see `Over.isLeftAdjoint_post`.
2. Restrict the structural map through the product comparison. Tensor pullback and
   restriction identify `f_A* r_Y` with `r_X f*`; `module_pullback_tensor_iso` fixes this on
   scalar insertions. The module adjunction is `module_pullback_pushforward_adjunction`.
3. On modules, the right adjoint sends `E × f⁻¹A` to `A × f_*E`; its operations agree with
   the induced ones. This gives delta. `geometric_module_transport` identifies its transpose
   with restriction of the ordinary transpose, so sigma and delta are mates.
4. Restrictions are exact with exact additive left adjoints. Thus
   `Functor.mapDerivedCategoryFactors.{w, w}` gives their termwise derived factorization, and
   `Adjunction.preservesKInjectiveComplexes` gives K-injectivity after restriction.
   `isKFlat_ringedToposPullback` gives K-flatness and flat terms after restriction.
5. Define beta on K-injectives by Q(delta). The Hom bijection
   `CochainComplex.IsKInjective.Qh_map_bijective` proves independence and naturality.
6. Take theta to be the inverse adjunction mate of beta, using `mateEquiv`.
7. Transpose a K-injective resolution of f* T: the ordinary slice transpose is the
   restriction of that resolution after sigma_T, by step 3, degree by degree.
8. Apply `derivedAdjunctionOfResolvingClass` to the flat-term K-flat representative T and
   the K-injective target. The normalized derived transpose and step 7 give exactly
   `theta_representative`; cancel the localized restriction of the resolution map.
9. K-flat resolutions exist by `exists_isKFlatResolutionIndependentCoefficients`. Hence
   theta is invertible everywhere. Beta was already invertible. The mate transpose
   identity is precisely the displayed counit equation. No site functor, structural-map
   flatness or invertibility, or boundedness was used. -/
theorem ringedSheafSliceDerivedComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u))
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A)))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A))] :
    ∃ o : RingedSheafSliceOrdinaryComparison RX RY f A,
      HasRingedSheafSliceDerivedComparison.{u, w} o := by
  sorry

end CategoryTheory
