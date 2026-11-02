/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons
import all WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
import all WeilConjectures.AlgebraicGeometry.OpenScalarTensor.ScalarPullbackCompositionCoherence
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicConjugateComparisonTransport
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteDirectCounitFixedRealizationTransport
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting

/-! # Finite coefficient pullback coherence in fixed-scalar coordinates

Source: the finite-reduction proof Step 2, expanded presentation-reduction Step 7;
Stacks Project, sites-cohomology.tex, Tag 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

attribute [local instance 100000] proEtaleRingModules_hasDerivedCategory
attribute [local instance 200000] SheafOfModules.instAbelian
private noncomputable local instance (priority := 200000) finiteTensorFixedStalk (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} _

section Coordinates
variable {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]

end Coordinates

section Presentation
open CategoryTheory.Limits
attribute [local implicit_reducible] Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [dC : HasDerivedCategory C] [dD : HasDerivedCategory D]
  [dE : HasDerivedCategory E] [dF : HasDerivedCategory F]

end Presentation

namespace AlgebraicGeometry.Scheme
open CategoryTheory.Limits
open Opposite
open ProEtale.OpenScalarTensor
attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] MorphismProperty Scheme.ProEt Scheme.instCategoryProEt
  Category.opposite CategoryStruct.opposite Quiver.opposite

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option maxHeartbeats 2000000 in
-- Keep the ordinary adjunction models intact while comparing their sectionwise units.
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local implicit_reducible] sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory
  CategoryTheory.Equivalence.mk

end AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

-- Expose the cached ring operations to compare them with the canonical ULift instance.
set_option linter.auxLemma false in
attribute [local implicit_reducible] coefficientCommRing._aux_1 coefficientCommRing._aux_4
  coefficientCommRing._aux_8 coefficientCommRing._aux_13 coefficientCommRing._aux_16
  coefficientCommRing._aux_20 coefficientCommRing._aux_28 coefficientCommRing._aux_30
  coefficientCommRing._aux_32 coefficientCommRing._aux_34 coefficientCommRing._aux_41
  ULift.ring
attribute [local implicit_reducible] Coefficient coefficientCommRing
  sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence
  finiteReductionRawPullbackModel
attribute [local implicit_reducible] smoothPurityPullback finiteReductionPullback
  finiteTensorPullbackModel finiteTensorReduction sfIntrinsicPullback sfIntrinsicTransport
open CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

set_option maxHeartbeats 2000000 in
-- Normalize the coefficient alias before comparing the two realization presentations.
attribute [local implicit_reducible] finiteReduction ProEtale.scalarExtensionFunctor
end WeilConjectures.PurityFiniteSetting

private theorem presentation_unit (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (L : C ⥤ E) (G : E ⥤ F) [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompIso (e.inverse ⋙ L) G ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso e.inverse L)
        G.mapDerivedCategory).hom.app
        (e.functor.mapDerivedCategory.obj K) ≫
      (L.mapDerivedCategory ⋙ G.mapDerivedCategory).map
        (e.mapDerivedCategory.unitIso.inv.app K) =
      (Functor.mapDerivedCategorySquareIso (e.funInvIdAssoc (L ⋙ G)).symm).inv.app K := by
  have ha :
      ((Functor.mapDerivedCategoryCompIso e.inverse (L ⋙ G)) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso L G)).hom =
      (Functor.mapDerivedCategoryCompIso (e.inverse ⋙ L) G ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso e.inverse L)
          G.mapDerivedCategory).hom := by
    simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom] using
        Functor.mapDerivedCategoryCompIso_assoc e.inverse L G
  rw [← ha]
  let q := Functor.mapDerivedCategorySquareIso (e.funInvIdAssoc (L ⋙ G)).symm
  apply (cancel_mono (q.hom.app K)).mp
  change _ = q.inv.app K ≫ q.hom.app K
  rw [Iso.inv_hom_id_app, Category.assoc]
  erw [q.hom.naturality]
  rw [← Category.assoc, derived_square_coherence e L G]
  dsimp only [Functor.comp_map]
  erw [e.mapDerivedCategory.counitInv_app_functor]
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

private theorem finiteTensorPullbackComparison_realize (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteReduction m hm hmn X).map ((rawRealizationSquare P.Ring f).hom.app K) ≫
      (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
        (P.finiteReductionRingHom m hm hmn) X).hom.app ((P.smoothPurityPullback f).obj K) ≫
      (sfIntrinsicDerivedEquivalence X (P.finiteReductionSetting m hm).Ring).functor.map
        (P.finiteTensorPullbackComparison m hm hmn f K).hom =
    (ProEtale.tensorPullbackIso (P.finiteReductionRingHom m hm hmn) f).inv.app
        ((sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj K) ≫
      (proEtaleConstantRingDerivedPullback (P.finiteReductionSetting m hm).Ring f).map
        ((ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
          (P.finiteReductionRingHom m hm hmn) Y).hom.app K) ≫
      (rawRealizationSquare (P.finiteReductionSetting m hm).Ring f).hom.app
        ((P.finiteTensorReduction m hm hmn Y).obj K) := by
  dsimp (config := { instances := true }) only [Coefficient, coefficientCommRing] at K ⊢
  rw [← rawRealizationSquare_model P f K]
  delta finiteTensorPullbackComparison
  dsimp (config := { instances := true }) only [Coefficient, coefficientCommRing]
  simp only [Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  simp only [← (P.finiteReduction m hm hmn X).map_comp_assoc,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  delta finiteReductionPullbackComparison
  dsimp (config := { instances := true }) only [Coefficient, coefficientCommRing]
  simp only [Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  simp only [← (P.finiteReduction m hm hmn X).map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  erw [← reassoc_of% (((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel
    f).hom.naturality ((ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) Y).hom.app K))]
  erw [rawRealizationSquare_model (P.finiteReductionSetting m hm) f
    ((P.finiteTensorReduction m hm hmn Y).obj K)]
  rfl

private theorem rawRealizationSquare_model (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteReductionRawPullbackModel f).hom.app
        ((sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj K) ≫
      (P.finiteTensorPullbackModel f K).hom =
    (rawRealizationSquare P.Ring f).hom.app K := by
  dsimp (config := { instances := true }) only [Coefficient, coefficientCommRing] at K ⊢
  let dY : HasDerivedCategory.{u + 1} (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring))) :=
    inferInstanceAs (HasDerivedCategory.{u + 1}
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
  let dX : HasDerivedCategory.{u + 1} (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring))) :=
    inferInstanceAs (HasDerivedCategory.{u + 1}
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
  let := sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let := sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
  have hp := presentation_unit (dC := dY) (dE := dX)
    (dD := inferInstanceAs (HasDerivedCategory.{u + 2}
      (proEtaleRingModules Y (proEtaleConstantRing Y P.Ring))))
    (dF := inferInstanceAs (HasDerivedCategory.{u + 2}
      (proEtaleRingModules X (proEtaleConstantRing X P.Ring))))
    (sfIntrinsicModuleEquivalence Y P.Ring)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring)) f)
    (sfIntrinsicModuleEquivalence X P.Ring).functor K
  have hn : (P.finiteReductionPullbackPresentation f).choose =
      P.finiteReductionPullbackPresentationNative f :=
    eq_of_heq (P.finiteReductionPullbackPresentation f).choose_spec.1
  simp only [finiteReductionRawPullbackModel, hn, Iso.trans_hom, NatTrans.comp_app,
    rawRealizationSquare, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  rw [Category.assoc]
  congr 1

private def rawRealizationSquare (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicDerivedEquivalence Y A).functor ⋙ proEtaleConstantRingDerivedPullback A f ≅
      ProEtale.sfFixedDerivedPullback A f ⋙ (sfIntrinsicDerivedEquivalence X A).functor :=
  Functor.isoWhiskerLeft _ (openSquareDerivedPullbackModel A f) ≪≫
    (exactRealizationSquare A f).symm

private def exactRealizationSquare (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.sfFixedDerivedPullback A f ⋙ (sfIntrinsicDerivedEquivalence X A).functor ≅
      (sfIntrinsicDerivedEquivalence Y A).functor ⋙ sfIntrinsicDerivedPullback A f :=
  Functor.mapDerivedCategorySquareIso
    ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ⋙
        (sfIntrinsicModuleEquivalence X A).functor)).symm
