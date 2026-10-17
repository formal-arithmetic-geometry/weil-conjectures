/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel
import Sheaf.Paper.IntegralResidueDerivedMonoidal
import Sheaf.Paper.IntegralResidueOrdinaryMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! Computation of the tensor-route in the residue tensor square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-model)

The target is the explicit ordinary homotopy tensor model. -/

@[expose] public section




universe v u v' u'

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory
variable {C : Type u} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
attribute [local instance] DerivedCategory.braidedCategory
private theorem quotientBraiding (K L : HomotopyCategory C (.up ℤ)) :
    (β_ (DerivedCategory.Qh.obj K) (DerivedCategory.Qh.obj L)).hom ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh L K =
      Functor.LaxMonoidal.μ DerivedCategory.Qh K L ≫
        DerivedCategory.Qh.map (β_ K L).hom :=
  DerivedMonoidal.braiding_hom_μ (DerivedCategory.Qh (C := C))
    (HomotopyCategory.quasiIso C (.up ℤ)) K L

private theorem quotientBraidingInv (K L : HomotopyCategory C (.up ℤ)) :
    (β_ (DerivedCategory.Qh.obj K) (DerivedCategory.Qh.obj L)).inv ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh K L =
      Functor.LaxMonoidal.μ DerivedCategory.Qh L K ≫
        DerivedCategory.Qh.map (β_ K L).inv := by
  rw [← cancel_epi (β_ _ _).hom, Iso.hom_inv_id_assoc,
    reassoc_of% (quotientBraiding K L), ← DerivedCategory.Qh.map_comp,
    Iso.hom_inv_id, Functor.map_id, Category.comp_id]

private theorem normalizePresentation (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    (derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P) ≫
      (β_ ((DerivedCategory.singleFunctor C 0).obj B) (DerivedCategory.Qh.obj P)).inv ≫
      ((Functor.tensorModelCoefficientIso B).hom ▷ DerivedCategory.Qh.obj P) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh (Functor.tensorModelCoefficient B) P =
    ε.app P ≫ DerivedCategory.Qh.map ((homotopyTensorSingleIso B).inv.app P) := by
  unfold derivedTensorPresentationIso derivedTensorSingleIso
  simp only [Iso.trans_hom, NatTrans.comp_app]
  simp only [BraidedCategory.tensorLeftIsoTensorRight_hom_app, Category.assoc,
    Iso.hom_inv_id_assoc]
  change _ ≫ _ ≫ ((Functor.tensorModelCoefficientIso B).inv ▷ _) ≫
    ((Functor.tensorModelCoefficientIso B).hom ▷ _) ≫ _ = _
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  simp only [Functor.leftDerivedNatIso_hom]
  change _ ≫ _ ≫ (DerivedCategory.tensorLeftQhObjCounit
    (Functor.tensorModelCoefficient B)).app P = _
  rw [Functor.leftDerivedNatTrans_app]
  rw [Functor.leftDerivedNatTrans_app_assoc]
  simp

private theorem normalizePresentationRight (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    (derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P) ≫
      (DerivedCategory.Qh.obj P ◁ (Functor.tensorModelCoefficientIso B).hom) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh P (Functor.tensorModelCoefficient B) =
    ε.app P ≫ DerivedCategory.Qh.map ((homotopyTensorSingleIso B).inv.app P) ≫
      DerivedCategory.Qh.map (β_ (Functor.tensorModelCoefficient B) P).hom := by
  rw [← reassoc_of% (normalizePresentation B H ε P)]
  rw [← quotientBraiding, BraidedCategory.braiding_naturality_left_assoc]
  simp

variable {D : Type*} [Category.{v + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]

/-- The generic tensor-route computation from the canonical tensor counit.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-calculation)
Proof. Normalize the tensor presentation, move the coefficient comparison through the
derived tensor comparison by naturality, apply its counit equation, use ordinary homotopy
braiding compatibility, cancel the braidings and apply counit naturality. -/
theorem residueTensorRoute_generic (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.IsLeftAdjoint]
    [F.Monoidal] [F.PreservesFlat]
    (hF : ∀ K L : C, F.map (β_ K L).hom ≫ Functor.OplaxMonoidal.δ F L K =
      Functor.OplaxMonoidal.δ F K L ≫ (β_ (F.obj K) (F.obj L)).hom)
    (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.map
        ((derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P)) ≫
      (F.leftDerivedTensorComparison.app (DerivedCategory.Qh.obj P)).app
        ((DerivedCategory.singleFunctor C 0).obj B) ≫
      Functor.tensorModelTarget F B P = Functor.tensorModelMap F B H ε P := by
  rw [Functor.tensorModelTarget_eq]
  unfold Functor.tensorModelMap
  rw [← BraidedCategory.braiding_inv_naturality_assoc]
  dsimp only [Functor.comp_obj]
  rw [quotientBraidingInv]
  have ht :
      (F.leftDerivedFunctorCounit.app P ⊗ₘ
        (F.leftDerivedFunctor.map (Functor.tensorModelCoefficientIso B).hom ≫
          F.leftDerivedFunctorCounit.app (Functor.tensorModelCoefficient B))) =
      (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P) ◁
        F.leftDerivedFunctor.map (Functor.tensorModelCoefficientIso B).hom) ≫
        (F.leftDerivedFunctorCounit.app P ⊗ₘ
          F.leftDerivedFunctorCounit.app (Functor.tensorModelCoefficient B)) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [ht]
  simp only [Category.assoc]
  rw [Functor.OplaxMonoidal.app_app_comp_whiskerLeft_assoc]
  rw [F.leftDerivedTensorComparison_app_app_comp_tensorHom_assoc]
  rw [← F.leftDerivedFunctor.map_comp_assoc, ← F.leftDerivedFunctor.map_comp_assoc,
    Category.assoc, normalizePresentationRight, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc]
  have hn := F.leftDerivedFunctorCounit.naturality
    (β_ (Functor.tensorModelCoefficient B) P).hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp]
  have hb := Functor.mapHomotopyCategory_map_braiding_hom_δ F hF
    (Functor.tensorModelCoefficient B) P
  change _ ≫ ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app
    (Functor.tensorModelCoefficient B) = _ at hb
  rw [hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he := F.leftDerivedFunctorCounit.naturality ((homotopyTensorSingleIso B).inv.app P)
  dsimp only [Functor.comp_map] at he
  erw [reassoc_of% he, ← DerivedCategory.Qh.map_comp]
  rfl

end CategoryTheory

namespace CategoryTheory.Mod.ResidueOrdinary
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]
  {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided] [G.PreservesEpimorphisms]
  (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]
private theorem braidComparison (M N : Mod C R) :
    (mapModComap ρ).map (β_ M N).hom ≫ (tensorComparison ρ N M).hom =
      (tensorComparison ρ M N).hom ≫
        (β_ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N)).hom := by
  apply Mod.hom_ext
  rw [← cancel_epi (G.map (tensorObjπ M N))]
  simp only [Mod.comp_hom']
  change G.map (tensorObjπ M N) ≫ G.map (β_ M N).hom.hom ≫ _ = _
  rw [← G.map_comp_assoc, Mod.braiding_hom_hom,
    Mod.tensorObjπ_braidingHomX, G.map_comp, Category.assoc,
    tensorComparison_π, reassoc_of% tensorComparison_π]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX]
  rw [← cancel_epi (Functor.LaxMonoidal.μ G M.X N.X)]
  simp only [IsIso.hom_inv_id_assoc]
  rw [Functor.LaxBraided.braided_assoc, IsIso.hom_inv_id_assoc]
  rfl
end CategoryTheory.Mod.ResidueOrdinary

namespace CategoryTheory.Functor.Monoidal
private theorem braidTransport {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
    (hF : ∀ X Y, F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) (X Y : C) :
    letI := transport i
    G.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ G Y X =
      Functor.OplaxMonoidal.δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom := by
  letI := transport i
  rw [transport_δ, transport_δ, i.inv.naturality_assoc, reassoc_of% hF X Y]
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality]
end CategoryTheory.Functor.Monoidal

namespace AlgebraicGeometry.ProEtale.CondensedRing
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
/-- Ordinary pullback preserves the braiding of balanced internal-module tensors.
Source: the balanced tensor presentation, Bhatt--Scholze, Lemma 6.5.9(3).
(blueprint: new-integral-residue-tensor-route-calculation)
Proof. Check the identity on balanced tensor presentation epimorphisms, using the ambient
braiding, then transport along the coefficient-pullback isomorphism. -/
theorem residueOrdinaryPullBraid
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    letI := residueOrdinaryUpperStarMonoidal Λ f
    (f)^*⟦Λ⟧.map (β_ M N).hom ≫ Functor.OplaxMonoidal.δ (f)^*⟦Λ⟧ N M =
      Functor.OplaxMonoidal.δ (f)^*⟦Λ⟧ M N ≫
        (β_ ((f)^*⟦Λ⟧.obj M) ((f)^*⟦Λ⟧.obj N)).hom := by
  rw [residueOrdinaryUpperStarMonoidal_eq]
  let G := (f)^*[Ab.{u + 1}]
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  letI : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  exact Functor.Monoidal.braidTransport
    (Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).symm
    (Mod.ResidueOrdinary.braidComparison ρ) M N
end AlgebraicGeometry.ProEtale.CondensedRing



open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]


/-- Compute the tensor-route against the ordinary homotopy tensor model.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-model)

Proof. Use the counit normalization of the fixed derived tensor presentation.
Move the coefficient single-functor comparison through the tensor comparison by
naturality. Compatibility of the derived tensor comparison with symmetry moves
the fixed coefficient to the first tensor factor. Its defining counit identity
then replaces the derived tensor comparison by Qh of the ordinary tensor
comparison. Naturality of the exact-pullback counit moves the homotopy
single-tensor comparison through it. The resulting composite is precisely
the displayed tensor model map. Every equality is an identity of natural
transformations, so no flatness of the residue coefficient or of P is required. -/
theorem integralResidue_tensorRoute_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    letI := residueExchangePullMonoidal ℓ E f
      (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
    let M := DerivedCategory.Qh.obj P
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
          ((residueExchangeTensorIso ℓ E Y).hom.app M) ≫
        Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
          M (residueExchangeCoefficient ℓ E Y) ≫
        residueExchangeTensorModelTarget ℓ E f P =
      residueExchangeTensorModelMap ℓ E f P := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
