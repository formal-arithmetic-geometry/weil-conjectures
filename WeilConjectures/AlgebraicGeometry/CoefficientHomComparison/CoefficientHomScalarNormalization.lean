/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import all WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedHomComparisonShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidalComp
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal

/-! # Native scalar normalization for closed comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

attribute [local instance] Functor.postcompose_left_commShift
  Functor.postcompose_right_commShift Functor.precompose_left_commShift
  Functor.precompose_right_commShift


private theorem monoidal_eq_of_delta {A B : Type*} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) (m n : F.Monoidal)
    (hd : ∀ K L, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F m.toOplaxMonoidal K L =
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F n.toOplaxMonoidal K L) : m = n := by
  letI := m
  have hu : @Functor.OplaxMonoidal.η _ _ _ _ _ _ F m.toOplaxMonoidal =
      @Functor.OplaxMonoidal.η _ _ _ _ _ _ F n.toOplaxMonoidal := by
    apply Functor.eq_of_leftUnitality (Functor.OplaxMonoidal.δ F (𝟙_ A) (𝟙_ A))
    · exact Functor.OplaxMonoidal.left_unitality_hom F (𝟙_ A)
    · rw [hd]
      exact @Functor.OplaxMonoidal.left_unitality_hom _ _ _ _ _ _ F n.toOplaxMonoidal (𝟙_ A)
  have hμ (K L : A) : @Functor.LaxMonoidal.μ _ _ _ _ _ _ F m.toLaxMonoidal K L =
      @Functor.LaxMonoidal.μ _ _ _ _ _ _ F n.toLaxMonoidal K L := by
    apply (cancel_mono (Functor.OplaxMonoidal.δ F K L)).1
    rw [Functor.Monoidal.μ_δ, hd]
    exact (@Functor.Monoidal.μ_δ _ _ _ _ _ _ F n K L).symm
  have hε : @Functor.LaxMonoidal.ε _ _ _ _ _ _ F m.toLaxMonoidal =
      @Functor.LaxMonoidal.ε _ _ _ _ _ _ F n.toLaxMonoidal := by
    apply (cancel_mono (Functor.OplaxMonoidal.η F)).1
    rw [Functor.Monoidal.ε_η, hu]
    exact (@Functor.Monoidal.ε_η _ _ _ _ _ _ F n).symm
  exact Functor.Monoidal.ext hε (funext fun K ↦ funext fun L ↦ hμ K L)
    hu (funext fun K ↦ funext fun L ↦ hd K L)

private theorem invert_normalization
    {A : Type*} [Category A] {X Y Z W : A} (b : X ≅ Y)
    (f : Y ⟶ Z) (g : X ⟶ W) (i : W ≅ Z)
    (h : b.hom ≫ f = g ≫ i.hom) : b.inv ≫ g = f ≫ i.inv := by
  apply (cancel_epi b.hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem left_identity_hom {A : Type*} [Category A] {F U : A ⥤ A}
    (a : F ⊣ U) (r : U ≅ 𝟭 A) (K : A) :
    (a.leftAdjointUniq (Adjunction.id.ofNatIsoRight r.symm)).hom.app K =
      F.map (r.inv.app K) ≫ a.counit.app K := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.id_unit,
    Functor.whiskerLeft_app, Category.id_comp]
  change r.inv.app K = a.homEquiv K K ((a.homEquiv K K).symm (r.inv.app K))
  exact (a.homEquiv _ _).apply_symm_apply _ |>.symm

private theorem normalized_transpose
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E : A ⥤ B} {U : B ⥤ A} {F : A' ⥤ B'} {V : B' ⥤ A'}
    (a : E ⊣ U) (d : F ⊣ V) (Q : A ⥤ A') (Q' : B ⥤ B')
    (ρ : Q' ⋙ V ≅ U ⋙ Q) (ε : Q ⋙ F ⟶ E ⋙ Q')
    (hu : ∀ P, d.unit.app (Q.obj P) ≫ V.map (ε.app P) ≫
      ρ.hom.app (E.obj P) = Q.map (a.unit.app P))
    (P : A) (H : B) (t : E.obj P ⟶ H) :
    d.homEquiv _ _ (ε.app P ≫ Q'.map t) =
      Q.map (a.homEquiv _ _ t) ≫ ρ.inv.app H := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  have h : d.unit.app (Q.obj P) ≫ V.map (ε.app P) =
      Q.map (a.unit.app P) ≫ ρ.inv.app (E.obj P) := by
    apply (cancel_mono (ρ.hom.app (E.obj P))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hu P
  rw [h, Category.assoc]
  erw [← ρ.inv.naturality]
  rw [Functor.comp_map, ← Category.assoc, ← Q.map_comp]
  rfl

private theorem conjugate_transpose
    {A B : Type*} [Category A] [Category B]
    {E F : A ⥤ B} {U V : B ⥤ A} (a : E ⊣ U) (b : F ⊣ V)
    (κ : U ≅ V) (K : A) (L : B) (t : F.obj K ⟶ L) :
    a.homEquiv _ _ (((conjugateEquiv b a).symm κ.inv).app K ≫ t) =
      b.homEquiv _ _ t ≫ κ.inv.app L := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit,
    ← unit_conjugateEquiv_symm b a κ.inv, Category.assoc]
  erw [← κ.inv.naturality]
  rw [← Category.assoc, b.homEquiv_unit]

private theorem conjugate_eq_leftAdjointUniq
    {A B : Type*} [Category A] [Category B]
    {E F : A ⥤ B} {U V : B ⥤ A} (a : E ⊣ U) (b : F ⊣ V) (κ : U ≅ V) :
    (conjugateIsoEquiv a b).symm κ = b.leftAdjointUniq (a.ofNatIsoRight κ) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  have h := unit_conjugateEquiv_symm a b κ.hom K
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  convert h.symm using 1 <;> rfl

private theorem map_homotopy_whisker_left
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) [F.Additive] {G H : B ⥤ C} [G.Additive] [H.Additive]
    (τ : G ⟶ H) (P : HomotopyCategory A (.up ℤ)) :
    (NatTrans.mapHomotopyCategory (Functor.whiskerLeft F τ) (.up ℤ)).app P =
      (NatTrans.mapHomotopyCategory τ (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rfl

private theorem map_homotopy_associator_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) [F.Additive] [G.Additive] [H.Additive]
    (P : HomotopyCategory A (.up ℤ)) :
    (NatTrans.mapHomotopyCategory (Functor.associator F G H).inv (.up ℤ)).app P = 𝟙 _ := by
  change (NatTrans.mapHomotopyCategory (𝟙 ((F ⋙ G) ⋙ H)) (.up ℤ)).app P = _
  rw [NatTrans.mapHomotopyCategory_id]
  rfl

section MonoidalDescent
variable {A B H : Type*} [Category A] [Category B] [Category H]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory H]
  {F G : B ⥤ H} [F.Monoidal] [G.Monoidal] (e : F ≅ G)

private theorem monoidal_delta (τ : F ⟶ G) [NatTrans.IsMonoidal τ] (K L : B) :
    τ.app (K ⊗ L) ≫ Functor.OplaxMonoidal.δ G K L =
      Functor.OplaxMonoidal.δ F K L ≫ (τ.app K ⊗ₘ τ.app L) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F K L)).1
  rw [Functor.Monoidal.μ_δ_assoc,
    ← Category.assoc, NatTrans.IsMonoidal.tensor, Category.assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

omit [MonoidalCategory A] in
private theorem monoidal_of_representatives (Q : A ⥤ B) (P : A → Prop)
    (hres : ∀ K : B, ∃ X, P X ∧ Nonempty (Q.obj X ≅ K))
    (h : ∀ X Y, P X → P Y →
      e.hom.app (Q.obj X ⊗ Q.obj Y) ≫ Functor.OplaxMonoidal.δ G (Q.obj X) (Q.obj Y) =
        Functor.OplaxMonoidal.δ F (Q.obj X) (Q.obj Y) ≫
          (e.hom.app (Q.obj X) ⊗ₘ e.hom.app (Q.obj Y))) :
    NatTrans.IsMonoidal e.hom := by
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro K L
  obtain ⟨X, hX, ⟨i⟩⟩ := hres K
  obtain ⟨Y, hY, ⟨j⟩⟩ := hres L
  apply (cancel_epi (F.map (i.hom ⊗ₘ j.hom))).1
  rw [e.hom.naturality_assoc, ← Functor.OplaxMonoidal.δ_natural,
    ← Functor.OplaxMonoidal.δ_natural_assoc, reassoc_of% (h X Y hX hY)]
  simp only [tensorHom_comp_tensorHom]
  rw [e.hom.naturality, e.hom.naturality]

private theorem monoidal_of_precomp (Q : A ⥤ B) [Q.LaxMonoidal]
    (P : A → Prop) (hres : ∀ K : B, ∃ X, P X ∧ Nonempty (Q.obj X ≅ K))
    (hμ : ∀ X Y, P X → P Y → IsIso (Functor.LaxMonoidal.μ Q X Y))
    [NatTrans.IsMonoidal (Functor.whiskerLeft Q e.hom)] :
    NatTrans.IsMonoidal e.hom := by
  apply monoidal_of_representatives e Q P hres
  intro X Y hX hY
  letI := hμ X Y hX hY
  have hh := NatTrans.IsMonoidal.tensor (τ := Functor.whiskerLeft Q e.hom) X Y
  simp only [Functor.LaxMonoidal.comp_μ, Functor.whiskerLeft_app, Category.assoc] at hh
  rw [e.hom.naturality] at hh
  simp only [← Category.assoc] at hh
  have hh' := (cancel_mono (G.map (Functor.LaxMonoidal.μ Q X Y))).1 hh
  apply (cancel_epi (Functor.LaxMonoidal.μ F (Q.obj X) (Q.obj Y))).1
  rw [Functor.Monoidal.μ_δ_assoc, reassoc_of% hh',
    Functor.Monoidal.μ_δ, Category.comp_id]
set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem monoidal_of_normalization {E₀ : Type*} [Category E₀]
    [MonoidalCategory E₀] (Q : A ⥤ B) [Q.LaxMonoidal]
    (V : E₀ ⥤ H) [V.LaxMonoidal]
    (T₁ T₂ : A ⥤ E₀) [T₁.Monoidal] [T₂.Monoidal]
    (cF : Q ⋙ F ⟶ T₁ ⋙ V) (cG : Q ⋙ G ⟶ T₂ ⋙ V)
    [NatTrans.IsMonoidal cF] [NatTrans.IsMonoidal cG]
    (θ : T₁ ≅ T₂) [NatTrans.IsMonoidal θ.hom]
    (hn : Functor.whiskerLeft Q e.hom ≫ cG =
      cF ≫ Functor.whiskerRight θ.hom V)
    (P : A → Prop) (hres : ∀ K : B, ∃ X, P X ∧ Nonempty (Q.obj X ≅ K))
    (hμ : ∀ X Y, P X → P Y → IsIso (Functor.LaxMonoidal.μ Q X Y))
    (hc : ∀ X Y, P X → P Y → IsIso (cG.app (X ⊗ Y))) :
    NatTrans.IsMonoidal e.hom := by
  haveI : NatTrans.IsMonoidal (Functor.whiskerLeft Q e.hom ≫ cG) := by
    rw [hn]
    infer_instance
  apply monoidal_of_representatives e Q P hres
  intro X Y hX hY
  letI := hμ X Y hX hY
  letI := hc X Y hX hY
  have hh := NatTrans.IsMonoidal.tensor
    (τ := Functor.whiskerLeft Q e.hom ≫ cG) X Y
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    ← tensorHom_comp_tensorHom, Category.assoc] at hh
  rw [← NatTrans.IsMonoidal.tensor (τ := cG)] at hh
  have hh' := (cancel_mono (cG.app (X ⊗ Y))).1
    (show (Functor.LaxMonoidal.μ (Q ⋙ F) X Y ≫ e.hom.app (Q.obj (X ⊗ Y))) ≫
        cG.app (X ⊗ Y) =
      ((e.hom.app (Q.obj X) ⊗ₘ e.hom.app (Q.obj Y)) ≫
        Functor.LaxMonoidal.μ (Q ⋙ G) X Y) ≫ cG.app (X ⊗ Y) by
      simpa only [Category.assoc] using hh)
  simp only [Functor.LaxMonoidal.comp_μ, Category.assoc] at hh'
  rw [e.hom.naturality] at hh'
  simp only [← Category.assoc] at hh'
  have hh'' := (cancel_mono (G.map (Functor.LaxMonoidal.μ Q X Y))).1 hh'
  apply (cancel_epi (Functor.LaxMonoidal.μ F (Q.obj X) (Q.obj Y))).1
  rw [Functor.Monoidal.μ_δ_assoc, reassoc_of% hh'',
    Functor.Monoidal.μ_δ, Category.comp_id]

end MonoidalDescent

section TensorShift

universe v c d
variable {C : Type c} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D' : Type d} [Category.{v + 1} D'] [Abelian D']
  [IsGrothendieckAbelian.{v + 1} D'] [MonoidalCategory D'] [MonoidalPreadditive D']
  [MonoidalClosed D'] [BraidedCategory D'] [Abelian.HasFunctorialFlatResolution D']
  (E : C ⥤ D') (U : D' ⥤ C) [E.Additive] [U.Additive]
  [E.PreservesKFlatQuasiIso] [E.PreservesFlat] [E.IsLeftAdjoint] [E.Monoidal]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : E ⊣ U)

attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

private theorem tensor_left_shift (K : DerivedCategory C) :
    letI := (adj.derivedAdjunction.ofNatIsoRight
      U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
    NatTrans.CommShift (E.leftDerivedTensorComparison.app K) ℤ := by
  let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  letI := b.leftAdjointCommShift ℤ
  have := Functor.derived_counit_commShift E U adj
  exact Functor.nativeLeft_commShift E K

private theorem tensor_right_shift (K : DerivedCategory C) :
    letI := (adj.derivedAdjunction.ofNatIsoRight
      U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
    NatTrans.CommShift (E.leftDerivedTensorComparison.flipApp K) ℤ := by
  let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  letI := b.leftAdjointCommShift ℤ
  have := Functor.derived_counit_commShift E U adj
  exact Functor.nativeRight_commShift E K

set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem tensor_shift_interchange (K X : DerivedCategory C) (n : ℤ) :
    letI := (adj.derivedAdjunction.ofNatIsoRight
      U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
    letI := E.leftDerivedFunctorMonoidal
    E.leftDerivedFunctor.obj K ◁ (E.leftDerivedFunctor.commShiftIso n).inv.app X ≫
        Functor.LaxMonoidal.μ E.leftDerivedFunctor K (X⟦n⟧) ≫
        E.leftDerivedFunctor.map (((tensorLeft K).commShiftIso n ≪≫
          (siteHomTensorParameterShift K n).symm).hom.app X) =
      (((tensorLeft (E.leftDerivedFunctor.obj K)).commShiftIso n ≪≫
        (siteHomTensorParameterShift (E.leftDerivedFunctor.obj K) n).symm).hom.app
          (E.leftDerivedFunctor.obj X)) ≫
        ((E.leftDerivedFunctor.commShiftIso n).inv.app K ▷ E.leftDerivedFunctor.obj X) ≫
        Functor.LaxMonoidal.μ E.leftDerivedFunctor (K⟦n⟧) X := by
  let G := E.leftDerivedFunctor
  letI := (adj.derivedAdjunction.ofNatIsoRight
    U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
  letI := E.leftDerivedFunctorMonoidal
  let δL : tensorLeft K ⋙ E.leftDerivedFunctor ⟶
      E.leftDerivedFunctor ⋙ tensorLeft (E.leftDerivedFunctor.obj K) :=
    E.leftDerivedTensorComparison.app K
  let δR : tensorRight X ⋙ E.leftDerivedFunctor ⟶
      E.leftDerivedFunctor ⋙ tensorRight (E.leftDerivedFunctor.obj X) :=
    E.leftDerivedTensorComparison.flipApp X
  haveI : NatTrans.CommShift δL ℤ := tensor_left_shift E U adj K
  haveI : NatTrans.CommShift δR ℤ := tensor_right_shift E U adj X
  have hL := NatTrans.shift_app_comm δL n X
  have hR := NatTrans.shift_app_comm δR n K
  simp only [Functor.commShiftIso_comp_hom_app] at hL hR
  dsimp [δL, δR] at hL hR
  have hL' : G.map (((tensorLeft K).commShiftIso n).hom.app X) ≫
        (G.commShiftIso n).hom.app (K ⊗ X) ≫ (Functor.OplaxMonoidal.δ G K X)⟦n⟧' =
      Functor.OplaxMonoidal.δ G K (X⟦n⟧) ≫ G.obj K ◁ (G.commShiftIso n).hom.app X ≫
        ((tensorLeft (G.obj K)).commShiftIso n).hom.app (G.obj X) := by
    dsimp only [G]
    rw [Functor.leftDerivedFunctorMonoidal_δ, Functor.leftDerivedFunctorMonoidal_δ]
    simpa only [Category.assoc] using hL
  have hR' : G.map (((tensorRight X).commShiftIso n).hom.app K) ≫
        (G.commShiftIso n).hom.app (K ⊗ X) ≫ (Functor.OplaxMonoidal.δ G K X)⟦n⟧' =
      Functor.OplaxMonoidal.δ G (K⟦n⟧) X ≫ (G.commShiftIso n).hom.app K ▷ G.obj X ≫
        ((tensorRight (G.obj X)).commShiftIso n).hom.app (G.obj K) := by
    dsimp only [G]
    rw [Functor.leftDerivedFunctorMonoidal_δ, Functor.leftDerivedFunctorMonoidal_δ]
    simpa only [Category.assoc] using hR
  apply (cancel_epi (Functor.OplaxMonoidal.δ G K (X⟦n⟧) ≫
    G.obj K ◁ (G.commShiftIso n).hom.app X)).mp
  apply (cancel_mono (Functor.OplaxMonoidal.δ G (K⟦n⟧) X ≫
    (G.commShiftIso n).hom.app K ▷ G.obj X ≫
      ((tensorRight (G.obj X)).commShiftIso n).hom.app (G.obj K))).mp
  dsimp only [G, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [siteHomTensorParameterShift, NatIso.ofComponents_inv_app, Iso.app_inv,
    Functor.map_comp, Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.hom_inv_id_app, Category.id_comp, Functor.Monoidal.μ_δ_assoc,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id_app, id_whiskerRight]
  rw [← hR']
  dsimp only [G, Functor.comp_obj] at hL' hR' ⊢
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp, Functor.Monoidal.δ_μ_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simpa only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj,
    Category.comp_id] using hL'


set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem source_shift_comparison_reindex (K M : DerivedCategory C)
    (p q : ℤ) (hp : -p = q) :
    letI := (adj.derivedAdjunction.ofNatIsoRight
      U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
    letI := E.leftDerivedFunctorMonoidal
    E.leftDerivedFunctor.map (((siteHomSourceShift K p) ≪≫
        Functor.isoWhiskerLeft (ihom K)
          (eqToIso (congrArg (shiftFunctor (DerivedCategory C)) hp))).hom.app M) ≫
        (E.leftDerivedFunctor.commShiftIso q).hom.app ((ihom K).obj M) ≫
        ((Functor.LaxMonoidal.ihomComparison E.leftDerivedFunctor K).natTrans.app M)⟦q⟧' =
      (Functor.LaxMonoidal.ihomComparison E.leftDerivedFunctor (K⟦p⟧)).natTrans.app M ≫
        (MonoidalClosed.pre ((E.leftDerivedFunctor.commShiftIso p).inv.app K)).app
          (E.leftDerivedFunctor.obj M) ≫
        (((siteHomSourceShift (E.leftDerivedFunctor.obj K) p) ≪≫
          Functor.isoWhiskerLeft (ihom (E.leftDerivedFunctor.obj K))
            (eqToIso (congrArg (shiftFunctor (DerivedCategory D')) hp))).hom.app
              (E.leftDerivedFunctor.obj M)) := by
  subst q
  letI := (adj.derivedAdjunction.ofNatIsoRight
    U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
  letI := E.leftDerivedFunctorMonoidal
  simpa using Functor.sourceShift_comparison E.leftDerivedFunctor K M p
    (fun X ↦ tensor_shift_interchange E U adj K X p)


set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem opposite_source_shift_comparison (K M : DerivedCategory C) (n : ℤ) :
    letI := (adj.derivedAdjunction.ofNatIsoRight
      U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
    letI := E.leftDerivedFunctorMonoidal
    E.leftDerivedFunctor.map ((siteHomOppositeSourceShift K n).hom.app M) ≫
        (E.leftDerivedFunctor.commShiftIso n).hom.app ((ihom K).obj M) ≫
        ((Functor.LaxMonoidal.ihomComparison E.leftDerivedFunctor K).natTrans.app M)⟦n⟧' =
      (Functor.LaxMonoidal.ihomComparison E.leftDerivedFunctor (K⟦-n⟧)).natTrans.app M ≫
        (MonoidalClosed.pre ((E.leftDerivedFunctor.commShiftIso (-n)).inv.app K)).app
          (E.leftDerivedFunctor.obj M) ≫
        (siteHomOppositeSourceShift (E.leftDerivedFunctor.obj K) n).hom.app
          (E.leftDerivedFunctor.obj M) := by
  letI := (adj.derivedAdjunction.ofNatIsoRight
    U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
  letI := E.leftDerivedFunctorMonoidal
  simpa only [siteHomOppositeSourceShift] using
    source_shift_comparison_reindex E U adj K M (-n) n (neg_neg n)



@[instance_reducible]
private def homotopy_monoidal : (E.mapHomotopyCategory (.up ℤ)).Monoidal := by
  letI := Functor.mapHomotopyCategoryOplaxMonoidal E
  haveI : IsIso (Functor.OplaxMonoidal.η (E.mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    infer_instance
  haveI (P Q : HomotopyCategory C (.up ℤ)) :
      IsIso (Functor.OplaxMonoidal.δ (E.mapHomotopyCategory (.up ℤ)) P Q) :=
    inferInstanceAs (IsIso (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans
      (.up ℤ) E).app P).app Q))
  exact .ofOplaxMonoidal _

private theorem derived_counit_monoidal :
    letI := homotopy_monoidal E
    letI := E.leftDerivedFunctorMonoidal
    NatTrans.IsMonoidal E.leftDerivedFunctorCounit := by
  letI := homotopy_monoidal E
  letI := E.leftDerivedFunctorMonoidal
  haveI := DerivedCategory.isIso_ε_Qh D'
  apply CategoryTheory.ExactMonoidalEquivalenceDerived.square_monoidal
    DerivedCategory.Qh DerivedCategory.Qh (E.mapHomotopyCategory (.up ℤ))
    E.leftDerivedFunctor E.leftDerivedFunctorCounit
  · rfl
  · exact Functor.leftDerivedTensorComparison_app_app_comp_tensorHom E

section Identity
variable (F : C ⥤ C) [F.Additive] [F.Monoidal] [F.IsLeftAdjoint]

private def cochain_iso_id (e : F ≅ 𝟭 C) :
    F.mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex C ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso C (.up ℤ)

private def homotopy_iso_id (e : F ≅ 𝟭 C) :
    F.mapHomotopyCategory (.up ℤ) ≅ 𝟭 (HomotopyCategory C (.up ℤ)) :=
  { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
    hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp,
      e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp,
      e.inv_hom_id, NatTrans.mapHomotopyCategory_id] } ≪≫
    Functor.mapHomotopyCategoryIdIso C (.up ℤ)

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem cochain_iso_id_monoidal (e : F ≅ 𝟭 C) [NatTrans.IsMonoidal e.hom] :
    NatTrans.IsMonoidal (cochain_iso_id F e).hom := by
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro P Q
  apply (cancel_epi (F.mapCochainComplexμIso P Q).hom).1
  simp only [Functor.OplaxMonoidal.id_δ, Category.comp_id,
    Functor.mapCochainComplex_δ, ← Functor.mapCochainComplexμIso_inv,
    Iso.hom_inv_id_assoc]
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f]
  erw [Functor.ιTensorObj_mapCochainComplexμIso_hom_f_assoc,
    CochainComplex.ιTensorObj_tensorHom_f]
  simp only [cochain_iso_id, Iso.trans_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f]
  change Functor.LaxMonoidal.μ F (P.X p) (Q.X q) ≫
      F.map (P.ιTensorObj Q p q n hpq) ≫ (e.hom.app ((P ⊗ Q).X n) ≫ 𝟙 _) =
    ((e.hom.app (P.X p) ≫ 𝟙 _) ⊗ₘ (e.hom.app (Q.X q) ≫ 𝟙 _)) ≫
      P.ιTensorObj Q p q n hpq
  simp only [Category.comp_id]
  erw [e.hom.naturality]
  have he := NatTrans.IsMonoidal.tensor (τ := e.hom) (P.X p) (Q.X q)
  simp only [Functor.LaxMonoidal.id_μ, Category.comp_id] at he
  rw [← Category.assoc, he]
  rfl



omit [IsGrothendieckAbelian.{v + 1, v + 1, c} C]
    [MonoidalCategory C]
    [MonoidalPreadditive C]
    [MonoidalClosed C]
    [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [F.Monoidal]
    [F.IsLeftAdjoint] in
private theorem homotopy_iso_id_quotient (e : F ≅ 𝟭 C) (P : CochainComplex C ℤ) :
    (homotopy_iso_id F e).hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      (HomotopyCategory.quotient C (.up ℤ)).map ((cochain_iso_id F e).hom.app P) := by
  simp only [homotopy_iso_id, cochain_iso_id, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapHomotopyCategoryIdIso_hom_app, Functor.map_comp]
  rfl

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem homotopy_iso_id_monoidal (e : F ≅ 𝟭 C) [NatTrans.IsMonoidal e.hom] :
    letI := homotopy_monoidal F
    NatTrans.IsMonoidal (homotopy_iso_id F e).hom := by
  letI := homotopy_monoidal F
  haveI := cochain_iso_id_monoidal F e
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro P Q
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
  have hc : (cochain_iso_id F e).hom.app (P ⊗ Q) =
      Functor.OplaxMonoidal.δ (F.mapHomologicalComplex (.up ℤ)) P Q ≫
        ((cochain_iso_id F e).hom.app P ⊗ₘ (cochain_iso_id F e).hom.app Q) := by
    apply (cancel_epi (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (.up ℤ)) P Q)).1
    rw [Functor.Monoidal.μ_δ_assoc]
    simpa only [Functor.LaxMonoidal.id_μ, Category.comp_id] using
      NatTrans.IsMonoidal.tensor (τ := (cochain_iso_id F e).hom) P Q
  have h := (HomotopyCategory.quotient C (.up ℤ)).congr_map hc
  change (homotopy_iso_id F e).hom.app
    ((HomotopyCategory.quotient C (.up ℤ)).obj (P ⊗ Q)) ≫ _ = _
  -- The quotient preserves the tensor maps, whose comparison components are identities.
  simp only [homotopy_iso_id_quotient, Functor.map_comp,
    Functor.mapHomotopyCategory_δ,
    Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app,
    Functor.mapCochainComplex_δ, Functor.OplaxMonoidal.id_δ,
    Functor.id_obj, MonoidalCategory.tensorHom_def,
    HomotopyCategory.MonoidalCategory.quotient_map_whiskerRight',
    HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft'] at h ⊢
  convert h using 1
  · rfl
  · exact Category.comp_id _
  · rfl

private theorem derived_id_monoidal [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
    (e : F ≅ 𝟭 C) [NatTrans.IsMonoidal e.hom]
    (α : F.leftDerivedFunctor ≅ 𝟭 (DerivedCategory C))
    (hα : ∀ P : HomotopyCategory C (.up ℤ),
      α.hom.app (DerivedCategory.Qh.obj P) = F.leftDerivedFunctorCounit.app P ≫
        DerivedCategory.Qh.map ((homotopy_iso_id F e).hom.app P)) :
    letI := F.leftDerivedFunctorMonoidal
    NatTrans.IsMonoidal α.hom := by
  letI := F.leftDerivedFunctorMonoidal
  letI := homotopy_monoidal F
  haveI := homotopy_iso_id_monoidal F e
  haveI := derived_counit_monoidal F
  have he : Functor.whiskerLeft DerivedCategory.Qh α.hom =
      F.leftDerivedFunctorCounit ≫
        Functor.whiskerRight (homotopy_iso_id F e).hom DerivedCategory.Qh ≫
        DerivedCategory.Qh.leftUnitor.hom ≫ DerivedCategory.Qh.rightUnitor.inv := by
    ext P
    simpa using hα P
  haveI : NatTrans.IsMonoidal (Functor.whiskerLeft DerivedCategory.Qh α.hom) := by
    rw [he]
    infer_instance
  apply monoidal_of_precomp α DerivedCategory.Qh F.kFlatKFlatMap
    F.exists_kFlatKFlatMap_iso
  intro P Q hP hQ
  exact Functor.isIso_μNatTrans_Qh_app_app_of_kFlat P Q hQ.1

end Identity

section MonoidalIso
variable (E' : C ⥤ D') [E'.Additive] [E'.PreservesKFlatQuasiIso]
  [E'.PreservesFlat] [E'.IsLeftAdjoint] [E'.Monoidal]

omit [MonoidalCategory D']
    [MonoidalPreadditive D']
    [MonoidalClosed D']
    [BraidedCategory D']
    [Abelian.HasFunctorialFlatResolution D']
    [E.PreservesFlat]
    [E.IsLeftAdjoint]
    [E.Monoidal]
    [E'.PreservesFlat]
    [E'.IsLeftAdjoint]
    [E'.Monoidal] in
@[reassoc]
private theorem iso_counit (e : E ≅ E') (P : HomotopyCategory C (.up ℤ)) :
    (Functor.leftDerivedFunctorIsoOfIso e).hom.app (DerivedCategory.Qh.obj P) ≫
        E'.leftDerivedFunctorCounit.app P =
      E.leftDerivedFunctorCounit.app P ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) := by
  exact Functor.leftDerivedNatTrans_app E.leftDerivedFunctor E'.leftDerivedFunctor
    E.leftDerivedFunctorCounit E'.leftDerivedFunctorCounit
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh) P

end MonoidalIso

section HomotopyComposition
variable {C₂ : Type*} [Category.{v + 1} C₂] [Abelian C₂]
  [IsGrothendieckAbelian.{v + 1} C₂] [MonoidalCategory C₂] [MonoidalPreadditive C₂]
  [MonoidalClosed C₂] [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]
  (F₂ : D' ⥤ C₂) [F₂.Additive] [F₂.Monoidal] [F₂.IsLeftAdjoint]
  (H₀ : C ⥤ C₂) [H₀.Additive] [H₀.Monoidal] [H₀.IsLeftAdjoint]

private def homotopy_comp_iso (e : H₀ ≅ E ⋙ F₂) :
    H₀.mapHomotopyCategory (.up ℤ) ≅
      E.mapHomotopyCategory (.up ℤ) ⋙ F₂.mapHomotopyCategory (.up ℤ) :=
  { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
    hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp,
      e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp,
      e.inv_hom_id, NatTrans.mapHomotopyCategory_id] } ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F₂)) (.up ℤ)).symm

omit [Abelian.HasFunctorialFlatResolution C]
    [Abelian.HasFunctorialFlatResolution D']
    [E.PreservesKFlatQuasiIso]
    [E.PreservesFlat]
    [Abelian.HasFunctorialFlatResolution C₂] in
private theorem homotopy_comp_iso_monoidal (e : H₀ ≅ E ⋙ F₂)
    [NatTrans.IsMonoidal e.hom] :
    letI := homotopy_monoidal E
    letI := homotopy_monoidal F₂
    letI := homotopy_monoidal H₀
    NatTrans.IsMonoidal (homotopy_comp_iso E F₂ H₀ e).hom := by
  letI := homotopy_monoidal E
  letI := homotopy_monoidal F₂
  letI := homotopy_monoidal H₀
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro P Q
  have he (K L : C) : Functor.OplaxMonoidal.δ H₀ K L ≫
      (e.hom.app K ⊗ₘ e.hom.app L) = e.hom.app (K ⊗ L) ≫
        F₂.map (Functor.OplaxMonoidal.δ E K L) ≫
        Functor.OplaxMonoidal.δ F₂ (E.obj K) (E.obj L) := by
    simpa only [Functor.OplaxMonoidal.comp_δ, Category.assoc] using
      (monoidal_delta e.hom K L).symm
  have h := Functor.mapHomotopyCategory_δ_comp_tensorHom he P Q
  simp only [Functor.OplaxMonoidal.comp_δ]
  convert h.symm using 1 <;> rfl

variable [F₂.PreservesKFlatQuasiIso] [F₂.PreservesFlat]
  [H₀.PreservesKFlatQuasiIso] [H₀.PreservesFlat]

private def composite_counit :
    DerivedCategory.Qh ⋙ (E.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor) ⟶
      (E.mapHomotopyCategory (.up ℤ) ⋙ F₂.mapHomotopyCategory (.up ℤ)) ⋙
        DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight E.leftDerivedFunctorCounit F₂.leftDerivedFunctor ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (E.mapHomotopyCategory (.up ℤ)) F₂.leftDerivedFunctorCounit ≫
    (Functor.associator _ _ _).inv

omit [E.PreservesFlat]
    [E.IsLeftAdjoint]
    [E.Monoidal]
    [MonoidalCategory C₂]
    [MonoidalPreadditive C₂]
    [MonoidalClosed C₂]
    [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₂]
    [F₂.Monoidal]
    [F₂.IsLeftAdjoint]
    [F₂.PreservesFlat] in
private theorem composite_counit_app (P : HomotopyCategory C (.up ℤ)) :
    (composite_counit E F₂).app P =
      F₂.leftDerivedFunctor.map (E.leftDerivedFunctorCounit.app P) ≫
        F₂.leftDerivedFunctorCounit.app ((E.mapHomotopyCategory (.up ℤ)).obj P) := by
  dsimp [composite_counit]
  simp only [Category.comp_id, Category.id_comp]

private theorem composite_counit_monoidal :
    letI := E.leftDerivedFunctorMonoidal
    letI := F₂.leftDerivedFunctorMonoidal
    letI := homotopy_monoidal E
    letI := homotopy_monoidal F₂
    NatTrans.IsMonoidal (composite_counit E F₂) := by
  letI := E.leftDerivedFunctorMonoidal
  letI := F₂.leftDerivedFunctorMonoidal
  letI := homotopy_monoidal E
  letI := homotopy_monoidal F₂
  haveI := derived_counit_monoidal E
  haveI := derived_counit_monoidal F₂
  unfold composite_counit
  infer_instance

set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem derived_comp_monoidal (e : H₀ ≅ E ⋙ F₂)
    [NatTrans.IsMonoidal e.hom]
    (α : H₀.leftDerivedFunctor ≅ E.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor)
    (hα : ∀ P : HomotopyCategory C (.up ℤ),
      α.hom.app (DerivedCategory.Qh.obj P) ≫ (composite_counit E F₂).app P =
        H₀.leftDerivedFunctorCounit.app P ≫
          DerivedCategory.Qh.map ((homotopy_comp_iso E F₂ H₀ e).hom.app P)) :
    letI := E.leftDerivedFunctorMonoidal
    letI := F₂.leftDerivedFunctorMonoidal
    letI := H₀.leftDerivedFunctorMonoidal
    NatTrans.IsMonoidal α.hom := by
  letI := E.leftDerivedFunctorMonoidal
  letI := F₂.leftDerivedFunctorMonoidal
  letI := H₀.leftDerivedFunctorMonoidal
  letI := homotopy_monoidal E
  letI := homotopy_monoidal F₂
  letI := homotopy_monoidal H₀
  haveI := derived_counit_monoidal H₀
  haveI := composite_counit_monoidal E F₂
  haveI := homotopy_comp_iso_monoidal E F₂ H₀ e
  apply monoidal_of_normalization α DerivedCategory.Qh DerivedCategory.Qh
    (H₀.mapHomotopyCategory (.up ℤ))
    (E.mapHomotopyCategory (.up ℤ) ⋙ F₂.mapHomotopyCategory (.up ℤ))
    H₀.leftDerivedFunctorCounit (composite_counit E F₂)
    (homotopy_comp_iso E F₂ H₀ e) (by ext P; exact hα P)
    E.kFlatKFlatMap E.exists_kFlatKFlatMap_iso
  · intro P Q hP hQ
    exact Functor.isIso_μNatTrans_Qh_app_app_of_kFlat P Q hQ.1
  · intro P Q hP hQ
    have hPQ : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat (P ⊗ Q) :=
      ObjectProperty.prop_tensor hP.1 hQ.1
    have hEPQ : (HomotopyCategory.quasiIso D' (.up ℤ)).kFlat
        ((E.mapHomotopyCategory (.up ℤ)).obj (P ⊗ Q)) :=
      ObjectProperty.prop_of_iso _
        (Functor.Monoidal.μIso (E.mapHomotopyCategory (.up ℤ)) P Q)
        (ObjectProperty.prop_tensor hP.2 hQ.2)
    haveI := E.isIso_leftDerivedFunctorCounit_app_of_kFlat' (P ⊗ Q) hPQ
    haveI := F₂.isIso_leftDerivedFunctorCounit_app_of_kFlat'
      ((E.mapHomotopyCategory (.up ℤ)).obj (P ⊗ Q)) hEPQ
    dsimp [composite_counit]
    infer_instance
omit [MonoidalCategory D']
    [MonoidalPreadditive D']
    [MonoidalClosed D']
    [BraidedCategory D']
    [Abelian.HasFunctorialFlatResolution D']
    [E.PreservesFlat]
    [E.IsLeftAdjoint]
    [E.Monoidal] in
private theorem exact_inverse_counit [PreservesFiniteLimits E]
    [PreservesFiniteColimits E] (P : HomotopyCategory C (.up ℤ)) :
    E.leftDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj P) ≫
      E.leftDerivedFunctorCounit.app P = E.mapDerivedCategoryFactorsh.hom.app P := by
  apply (cancel_epi (E.leftDerivedFunctorIsoMapDerivedCategory.hom.app
    (DerivedCategory.Qh.obj P))).1
  rw [Iso.hom_inv_id_app_assoc]
  exact (E.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac P).symm

omit [E.PreservesKFlatQuasiIso]
    [E.PreservesFlat]
    [E.IsLeftAdjoint]
    [E.Monoidal]
    [MonoidalCategory C₂]
    [MonoidalPreadditive C₂]
    [MonoidalClosed C₂]
    [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₂]
    [F₂.Monoidal]
    [F₂.IsLeftAdjoint]
    [F₂.PreservesFlat] in
private theorem mixed_left_counit [PreservesFiniteLimits E]
    [PreservesFiniteColimits E] [E.PreservesKFlatComplexes]
    (P : HomotopyCategory C (.up ℤ)) :
    (Functor.leftDerivedFunctorCompMapDerivedCategoryIso E F₂).hom.app
        (DerivedCategory.Qh.obj P) ≫
      F₂.leftDerivedFunctor.map (E.mapDerivedCategoryFactorsh.hom.app P) ≫
        F₂.leftDerivedFunctorCounit.app ((E.mapHomotopyCategory (.up ℤ)).obj P) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F₂)) (.up ℤ)).hom.app P) =
      (E ⋙ F₂).leftDerivedFunctorCounit.app P := by
  have h := Functor.leftDerivedNatTrans_app (E ⋙ F₂).leftDerivedFunctor
    (E.mapDerivedCategory ⋙ F₂.leftDerivedFunctor)
    (E ⋙ F₂).leftDerivedFunctorCounit
    (Functor.leftDerivedFunctorCompMapDerivedCategoryCounit E F₂)
    (HomotopyCategory.quasiIso C (.up ℤ)) (𝟙 _) P
  simpa [Functor.leftDerivedFunctorCompMapDerivedCategoryIso,
    Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
    Functor.leftDerivedFunctorCompMapDerivedCategoryCounit] using h

omit [MonoidalCategory D']
    [MonoidalPreadditive D']
    [MonoidalClosed D']
    [BraidedCategory D']
    [Abelian.HasFunctorialFlatResolution D']
    [E.PreservesFlat]
    [E.IsLeftAdjoint]
    [E.Monoidal]
    [MonoidalCategory C₂]
    [MonoidalPreadditive C₂]
    [MonoidalClosed C₂]
    [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₂]
    [F₂.Monoidal]
    [F₂.IsLeftAdjoint]
    [F₂.PreservesKFlatQuasiIso]
    [F₂.PreservesFlat] in
private theorem mixed_right_counit [PreservesFiniteLimits F₂]
    [PreservesFiniteColimits F₂] (P : HomotopyCategory C (.up ℤ)) :
    (Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso E F₂).hom.app
        (DerivedCategory.Qh.obj P) ≫
      F₂.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app P) ≫
        F₂.mapDerivedCategoryFactorsh.hom.app ((E.mapHomotopyCategory (.up ℤ)).obj P) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F₂)) (.up ℤ)).hom.app P) =
      (E ⋙ F₂).leftDerivedFunctorCounit.app P := by
  have h := Functor.leftDerivedNatTrans_app (E ⋙ F₂).leftDerivedFunctor
    (E.leftDerivedFunctor ⋙ F₂.mapDerivedCategory)
    (E ⋙ F₂).leftDerivedFunctorCounit
    (Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit E F₂)
    (HomotopyCategory.quasiIso C (.up ℤ)) (𝟙 _) P
  simpa [Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso,
    Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
    Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit] using h

private def right_exact_comparison [PreservesFiniteLimits F₂]
    [PreservesFiniteColimits F₂] :
    (E ⋙ F₂).leftDerivedFunctor ≅ E.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor :=
  Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso E F₂ ≪≫
    Functor.isoWhiskerLeft E.leftDerivedFunctor F₂.leftDerivedFunctorIsoMapDerivedCategory.symm

omit [E.PreservesFlat]
    [E.IsLeftAdjoint]
    [E.Monoidal]
    [MonoidalCategory C₂]
    [MonoidalPreadditive C₂]
    [MonoidalClosed C₂]
    [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₂]
    [F₂.Monoidal]
    [F₂.IsLeftAdjoint]
    [F₂.PreservesFlat] in
@[reassoc]
private theorem right_exact_comparison_counit [PreservesFiniteLimits F₂]
    [PreservesFiniteColimits F₂] (P : HomotopyCategory C (.up ℤ)) :
    (right_exact_comparison E F₂).hom.app (DerivedCategory.Qh.obj P) ≫
      F₂.leftDerivedFunctor.map (E.leftDerivedFunctorCounit.app P) ≫
        F₂.leftDerivedFunctorCounit.app ((E.mapHomotopyCategory (.up ℤ)).obj P) =
      (E ⋙ F₂).leftDerivedFunctorCounit.app P := by
  dsimp only [right_exact_comparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  rw [Category.assoc]
  erw [← F₂.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  erw [exact_inverse_counit F₂ ((E.mapHomotopyCategory (.up ℤ)).obj P)]
  have h := mixed_right_counit E F₂ P
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at h
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at h
  exact h

section Square
variable {B₂ : Type*} [Category.{v + 1} B₂] [Abelian B₂]
  [IsGrothendieckAbelian.{v + 1} B₂] [MonoidalCategory B₂] [MonoidalPreadditive B₂]
  [MonoidalClosed B₂] [BraidedCategory B₂] [Abelian.HasFunctorialFlatResolution B₂]
  (J : C ⥤ B₂) [J.Additive] [J.Monoidal] [J.IsLeftAdjoint]
  [J.PreservesKFlatQuasiIso] [J.PreservesFlat]
  (K : B₂ ⥤ C₂) [K.Additive] [K.Monoidal] [K.IsLeftAdjoint]
  [K.PreservesKFlatQuasiIso] [K.PreservesFlat]

private def homotopy_square_iso (e : E ⋙ F₂ ≅ J ⋙ K) :
    E.mapHomotopyCategory (.up ℤ) ⋙ F₂.mapHomotopyCategory (.up ℤ) ≅
      J.mapHomotopyCategory (.up ℤ) ⋙ K.mapHomotopyCategory (.up ℤ) :=
  (homotopy_comp_iso E F₂ (J ⋙ K) e.symm).symm ≪≫
    homotopy_comp_iso J K (J ⋙ K) (Iso.refl _)

set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem derived_square_monoidal (e : E ⋙ F₂ ≅ J ⋙ K)
    [NatTrans.IsMonoidal e.hom]
    (α : E.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor ≅
      J.leftDerivedFunctor ⋙ K.leftDerivedFunctor)
    (hα : ∀ P : HomotopyCategory C (.up ℤ),
      α.hom.app (DerivedCategory.Qh.obj P) ≫ (composite_counit J K).app P =
        (composite_counit E F₂).app P ≫
          DerivedCategory.Qh.map ((homotopy_square_iso E F₂ J K e).hom.app P)) :
    letI := E.leftDerivedFunctorMonoidal
    letI := F₂.leftDerivedFunctorMonoidal
    letI := J.leftDerivedFunctorMonoidal
    letI := K.leftDerivedFunctorMonoidal
    NatTrans.IsMonoidal α.hom := by
  letI := E.leftDerivedFunctorMonoidal
  letI := F₂.leftDerivedFunctorMonoidal
  letI := J.leftDerivedFunctorMonoidal
  letI := K.leftDerivedFunctorMonoidal
  letI := homotopy_monoidal E
  letI := homotopy_monoidal F₂
  letI := homotopy_monoidal J
  letI := homotopy_monoidal K
  letI := homotopy_monoidal (J ⋙ K)
  haveI := composite_counit_monoidal E F₂
  haveI := composite_counit_monoidal J K
  haveI : NatTrans.IsMonoidal e.symm.hom := by
    change NatTrans.IsMonoidal e.inv
    infer_instance
  haveI : NatTrans.IsMonoidal (Iso.refl (J ⋙ K)).hom := by
    change NatTrans.IsMonoidal (𝟙 (J ⋙ K))
    infer_instance
  haveI := homotopy_comp_iso_monoidal E F₂ (J ⋙ K) e.symm
  haveI := homotopy_comp_iso_monoidal J K (J ⋙ K) (Iso.refl _)
  haveI : NatTrans.IsMonoidal (homotopy_square_iso E F₂ J K e).hom := by
    dsimp only [homotopy_square_iso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  apply monoidal_of_normalization α DerivedCategory.Qh DerivedCategory.Qh
    (E.mapHomotopyCategory (.up ℤ) ⋙ F₂.mapHomotopyCategory (.up ℤ))
    (J.mapHomotopyCategory (.up ℤ) ⋙ K.mapHomotopyCategory (.up ℤ))
    (composite_counit E F₂) (composite_counit J K)
    (homotopy_square_iso E F₂ J K e) (by ext P; exact hα P)
    J.kFlatKFlatMap J.exists_kFlatKFlatMap_iso
  · intro P Q hP hQ
    exact Functor.isIso_μNatTrans_Qh_app_app_of_kFlat P Q hQ.1
  · intro P Q hP hQ
    have hPQ : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat (P ⊗ Q) :=
      ObjectProperty.prop_tensor hP.1 hQ.1
    have hJPQ : (HomotopyCategory.quasiIso B₂ (.up ℤ)).kFlat
        ((J.mapHomotopyCategory (.up ℤ)).obj (P ⊗ Q)) :=
      ObjectProperty.prop_of_iso _
        (Functor.Monoidal.μIso (J.mapHomotopyCategory (.up ℤ)) P Q)
        (ObjectProperty.prop_tensor hP.2 hQ.2)
    haveI := J.isIso_leftDerivedFunctorCounit_app_of_kFlat' (P ⊗ Q) hPQ
    haveI := K.isIso_leftDerivedFunctorCounit_app_of_kFlat'
      ((J.mapHomotopyCategory (.up ℤ)).obj (P ⊗ Q)) hJPQ
    rw [composite_counit_app]
    infer_instance
end Square

end HomotopyComposition

end TensorShift



private theorem scalar_monoidal_eq (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    CondensedRing.internalScalarMonoidal a X =
      Mod.extendScalarsMonoidal (coefficientMap a X) := by
  apply CondensedRing.normalized_unique a X
  · exact (CondensedRing.internalScalarMonoidalNormalized_existsUnique a X).exists.choose_spec
  · intro M N
    change Mod.tensorObjπ M N ≫
      (Mod.extendUnit (coefficientMap a X) (M ⊗ N)).hom ≫
      ((Mod.extendScalarsOplaxMonoidal (coefficientMap a X)).δ M N).hom = _
    rw [Mod.extendScalarsOplaxMonoidal_δ, Mod.extendUnit_hom,
      Mod.extendUnitHom_extendHom, Mod.comp_hom',
      Mod.tensorObjπ_tensorHom_hom_whisker_assoc, Mod.tensorObjπ_comapTensorHom_hom]
    simp only [MonoidalCategory.tensorHom_def, Category.assoc]
    rfl

section ModuleTower
universe v c
variable {C : Type c} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  {R S T : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  [MonObj T] [IsCommMonObj T]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]
  (χ : R ⟶ T) [IsMonHom χ] (h : φ ≫ ψ = χ)

private def module_ordinary_tower :
    Mod.extendScalars (χ) ≅
      Mod.extendScalars (φ) ⋙ Mod.extendScalars (ψ) :=
  (conjugateIsoEquiv
    ((Mod.extendRestrictAdjunction (φ)).comp
      (Mod.extendRestrictAdjunction (ψ)))
    (Mod.extendRestrictAdjunction (χ))).symm
    ((Mod.comapComp (φ) (ψ)).symm ≪≫
      Mod.comapCongr h)

private def module_ordinary_restriction_tower :
    Mod.comap (D := C) (ψ) ⋙ Mod.comap (D := C) (φ) ≅
      Mod.comap (D := C) (χ) :=
  (Mod.comapComp (φ) (ψ)).symm ≪≫
    Mod.comapCongr h

private def module_homotopy_restriction_tower :=
  Functor.mapHomotopyCategoryCompIso
    (Iso.refl (Mod.comap (D := C) (ψ) ⋙ Mod.comap (D := C) (φ))) (.up ℤ) ≪≫
  { hom := NatTrans.mapHomotopyCategory (module_ordinary_restriction_tower φ ψ χ h).hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory (module_ordinary_restriction_tower φ ψ χ h).inv (.up ℤ)
    hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp,
      Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp,
      Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id] }

omit [MonoidalPreadditive C]
    [Abelian.HasFunctorialFlatResolution C]
    [IsCommMonObj T] in
private theorem module_ordinary_tower_comp :
    module_ordinary_tower φ ψ (φ ≫ ψ) rfl = Mod.extendScalarsComp φ ψ := by
  have hk : module_ordinary_restriction_tower φ ψ (φ ≫ ψ) rfl =
      (Mod.comapComp (C := C) φ ψ).symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    simp only [module_ordinary_restriction_tower, Iso.trans_hom, NatTrans.comp_app,
      Mod.comp_hom', Mod.comapCongr_hom_app_hom]
    erw [Category.comp_id]
  change (conjugateIsoEquiv ((Mod.extendRestrictAdjunction φ).comp
    (Mod.extendRestrictAdjunction ψ)) (Mod.extendRestrictAdjunction (φ ≫ ψ))).symm
      (module_ordinary_restriction_tower φ ψ (φ ≫ ψ) rfl) = _
  rw [hk, conjugate_eq_leftAdjointUniq]
  rfl

private theorem module_transpose
    (P : HomotopyCategory
      (Mod C R) (.up ℤ))
    (H : HomotopyCategory
      (Mod C S) (.up ℤ))
    (t : ((Mod.extendScalars (φ)).mapHomotopyCategory (.up ℤ)).obj P ⟶ H) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction (φ)).homEquiv _ _
      ((Mod.extendScalars (φ)).leftDerivedFunctorCounit.app P ≫
        DerivedCategory.Qh.map t) =
      DerivedCategory.Qh.map
        (((Mod.extendRestrictAdjunction (φ)).mapHomotopyCategory
          (.up ℤ)).homEquiv _ _ t) ≫
        (Mod.comap (D := C) (φ)).mapDerivedCategoryFactorsh.inv.app H := by
  apply normalized_transpose
    ((Mod.extendRestrictAdjunction (φ)).mapHomotopyCategory (.up ℤ))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (φ))
    DerivedCategory.Qh DerivedCategory.Qh
    (Mod.comap (D := C) (φ)).mapDerivedCategoryFactorsh
    (Mod.extendScalars (φ)).leftDerivedFunctorCounit
  intro M
  rw [Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh_assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

omit [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [IsCommMonObj R]
    [IsCommMonObj S]
    [IsCommMonObj T] in
private theorem module_restriction_tower_factors
    (H : HomotopyCategory
      (Mod C T) (.up ℤ)) :
    (Mod.comap (D := C) (φ)).mapDerivedCategoryFactorsh.inv.app
        (((Mod.comap (D := C) (ψ)).mapHomotopyCategory (.up ℤ)).obj H) ≫
      (Mod.comap (D := C) (φ)).mapDerivedCategory.map
        ((Mod.comap (D := C) (ψ)).mapDerivedCategoryFactorsh.inv.app H) ≫
      (Mod.mapDerivedCategoryComapCompIso (φ) (ψ)
        (χ) h).hom.app
        (DerivedCategory.Qh.obj H) =
      DerivedCategory.Qh.map ((module_homotopy_restriction_tower φ ψ χ h).hom.app H) ≫
        (Mod.comap (D := C) (χ)).mapDerivedCategoryFactorsh.inv.app H := by
  simp only [Mod.mapDerivedCategoryComapCompIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_inv_app_assoc,
    Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app,
    ← DerivedCategory.Qh.map_comp_assoc]
  rfl

omit [Abelian.HasFunctorialFlatResolution C]
    [IsCommMonObj T] in
private theorem module_ordinary_tower_homotopy_unit
    (P : HomotopyCategory
      (Mod C R) (.up ℤ)) :
    (((Mod.extendRestrictAdjunction (φ)).mapHomotopyCategory (.up ℤ)).comp
      ((Mod.extendRestrictAdjunction (ψ)).mapHomotopyCategory (.up ℤ))).homEquiv
      _ _ ((homotopy_comp_iso (Mod.extendScalars (φ))
        (Mod.extendScalars (ψ))
        (Mod.extendScalars (χ)) (module_ordinary_tower φ ψ χ h)).inv.app P) ≫
      (module_homotopy_restriction_tower φ ψ χ h).hom.app
        (((Mod.extendScalars (χ)).mapHomotopyCategory (.up ℤ)).obj P) =
      ((Mod.extendRestrictAdjunction (χ)).mapHomotopyCategory
        (.up ℤ)).unit.app P := by
  let A := Mod.extendRestrictAdjunction (φ)
  let B := Mod.extendRestrictAdjunction (ψ)
  let H := Mod.extendRestrictAdjunction (χ)
  let κ := module_ordinary_restriction_tower φ ψ χ h
  let θ := module_ordinary_tower φ ψ χ h
  let cR := Functor.mapHomotopyCategoryCompIso (Iso.refl
    (Mod.comap (D := C) (ψ) ⋙
      Mod.comap (φ))) (.up ℤ)
  have hu (M) : (A.comp B).unit.app M ≫
      (Mod.comap (D := C) (ψ) ⋙
        Mod.comap (φ)).map (θ.inv.app M) =
      H.unit.app M ≫ κ.inv.app ((Mod.extendScalars (χ)).obj M) := by
    convert (unit_conjugateEquiv_symm H (A.comp B) κ.inv M).symm using 1 ; rfl
  have h := Adjunction.mapHomotopyCategory_unit_app_comp (.up ℤ)
    (A.comp B) H θ.inv κ.inv hu P
  have hh := congrArg (fun f ↦ f ≫
    (NatTrans.mapHomotopyCategory κ.hom (.up ℤ)).app
      (((Mod.extendScalars (χ)).mapHomotopyCategory (.up ℤ)).obj P)) h
  simp only [Category.assoc, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
    Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id, NatTrans.id_app
    ] at hh
  rw [Adjunction.mapHomotopyCategory_comp_unit_app] at hh
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  simp only [homotopy_comp_iso, module_homotopy_restriction_tower, Iso.trans_inv,
    Iso.trans_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Category.id_comp, Functor.comp_map,
    Category.assoc] at hh ⊢
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
    Category.comp_id] at hh
  convert hh using 1 <;> rfl

set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem module_tower_on_homotopy
    (P : HomotopyCategory
      (Mod C R) (.up ℤ)) :
    (Mod.derivedExtendScalarsCompIso φ ψ χ h).hom.app (DerivedCategory.Qh.obj P) ≫
        (composite_counit (Mod.extendScalars (φ))
          (Mod.extendScalars (ψ))).app P =
      (Mod.extendScalars (χ)).leftDerivedFunctorCounit.app P ≫
        DerivedCategory.Qh.map ((homotopy_comp_iso (Mod.extendScalars (φ))
          (Mod.extendScalars (ψ))
          (Mod.extendScalars (χ))
          (module_ordinary_tower φ ψ χ h)).hom.app P) := by
  letI := Mod.extendScalarsMonoidal φ
  letI := Mod.extendScalarsMonoidal ψ
  letI := Mod.extendScalarsMonoidal χ
  let A := Mod.derivedExtendMapDerivedCategoryAdjunction φ
  let B := Mod.derivedExtendMapDerivedCategoryAdjunction ψ
  let H := Mod.derivedExtendMapDerivedCategoryAdjunction χ
  let θ := homotopy_comp_iso (Mod.extendScalars φ) (Mod.extendScalars ψ)
    (Mod.extendScalars χ) (module_ordinary_tower φ ψ χ h)
  let κ := Mod.mapDerivedCategoryComapCompIso φ ψ χ h
  have hi : (Mod.derivedExtendScalarsCompIso φ ψ χ h).inv.app (DerivedCategory.Qh.obj P) ≫
      (Mod.extendScalars χ).leftDerivedFunctorCounit.app P =
      (composite_counit (Mod.extendScalars φ) (Mod.extendScalars ψ)).app P ≫
        DerivedCategory.Qh.map (θ.inv.app P) := by
    apply ((A.comp B).homEquiv _ _).injective
    apply (cancel_mono (κ.hom.app
      (DerivedCategory.Qh.obj (((Mod.extendScalars χ).mapHomotopyCategory (.up ℤ)).obj P)))).1
    change (A.comp B).homEquiv _ _
        (((conjugateEquiv H (A.comp B)).symm κ.inv).app _ ≫ _) ≫ _ = _
    rw [conjugate_transpose (A.comp B) H κ, Category.assoc]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    rw [composite_counit_app, Category.assoc]
    change _ = (A.comp B).homEquiv _ _
      ((Mod.extendScalars ψ).leftDerivedFunctor.map
          ((Mod.extendScalars φ).leftDerivedFunctorCounit.app P) ≫
        (Mod.extendScalars ψ).leftDerivedFunctorCounit.app _ ≫
        DerivedCategory.Qh.map (θ.inv.app P)) ≫ _
    rw [Adjunction.comp_homEquiv]
    erw [_root_.Equiv.trans_apply]
    erw [B.homEquiv_naturality_left, module_transpose ψ]
    let t := ((Mod.extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ)).homEquiv _ _
      (θ.inv.app P)
    erw [← Category.assoc
      ((Mod.extendScalars φ).leftDerivedFunctorCounit.app P)
      (DerivedCategory.Qh.map t)
      ((Mod.comap ψ).mapDerivedCategoryFactorsh.inv.app
        (((Mod.extendScalars χ).mapHomotopyCategory (.up ℤ)).obj P))]
    erw [A.homEquiv_naturality_right, module_transpose φ]
    simp only [Category.assoc]
    rw [module_restriction_tower_factors φ ψ χ h, ← DerivedCategory.Qh.map_comp_assoc]
    have hc := module_ordinary_tower_homotopy_unit φ ψ χ h P
    rw [Adjunction.comp_homEquiv] at hc
    erw [_root_.Equiv.trans_apply] at hc
    erw [hc]
    have hu := Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh χ P
    simpa only [H, Adjunction.homEquiv_unit] using hu
  apply (cancel_mono (DerivedCategory.Qh.map (θ.inv.app P))).1
  rw [Category.assoc, ← hi, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [Category.assoc, ← DerivedCategory.Qh.map_comp, Iso.hom_inv_id_app,
    DerivedCategory.Qh.map_id]
  exact (Category.comp_id _).symm

omit [MonoidalPreadditive C]
    [Abelian.HasFunctorialFlatResolution C] in
private theorem module_ordinary_tower_monoidal :
    letI := Mod.extendScalarsMonoidal φ
    letI := Mod.extendScalarsMonoidal ψ
    letI := Mod.extendScalarsMonoidal χ
    NatTrans.IsMonoidal (module_ordinary_tower φ ψ χ h).hom := by
  letI := Mod.extendScalarsMonoidal φ
  letI := Mod.extendScalarsMonoidal ψ
  letI := Mod.extendScalarsMonoidal χ
  letI := Mod.comapLaxMonoidal φ
  letI := Mod.comapLaxMonoidal ψ
  letI := Mod.comapLaxMonoidal χ
  letI := Mod.comapLaxMonoidal (φ ≫ ψ)
  let κ : (Mod.comap ψ : Mod C T ⥤ Mod C S) ⋙ Mod.comap φ ≅
      (Mod.comap χ : Mod C T ⥤ Mod C R) :=
    (Mod.comapComp φ ψ).symm ≪≫ Mod.comapCongr h
  haveI := Mod.isMonoidal_comapComp_hom φ ψ
  haveI := Mod.isMonoidal_comapCongr_hom h
  haveI : NatTrans.IsMonoidal κ.hom := by
    dsimp only [κ, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  haveI := Mod.isMonoidal_extendRestrictAdjunction φ
  haveI := Mod.isMonoidal_extendRestrictAdjunction ψ
  haveI := Mod.isMonoidal_extendRestrictAdjunction χ
  apply NatTrans.IsMonoidal.of_isIso_of_δ
  intro K L
  exact conjugateEquiv_symm_app_tensor_comp_δ
    ((Mod.extendRestrictAdjunction φ).comp (Mod.extendRestrictAdjunction ψ))
    (Mod.extendRestrictAdjunction χ) κ.hom K L

private theorem module_tower_monoidal :
    letI := Mod.extendScalarsMonoidal φ
    letI := Mod.extendScalarsMonoidal ψ
    letI := Mod.extendScalarsMonoidal χ
    letI := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
    letI := (Mod.extendScalars ψ).leftDerivedFunctorMonoidal
    letI := (Mod.extendScalars χ).leftDerivedFunctorMonoidal
    NatTrans.IsMonoidal (Mod.derivedExtendScalarsCompIso φ ψ χ h).hom := by
  letI := Mod.extendScalarsMonoidal φ
  letI := Mod.extendScalarsMonoidal ψ
  letI := Mod.extendScalarsMonoidal χ
  haveI := module_ordinary_tower_monoidal φ ψ χ h
  exact derived_comp_monoidal (Mod.extendScalars (φ))
    (Mod.extendScalars (ψ))
    (Mod.extendScalars (χ)) (module_ordinary_tower φ ψ χ h)
    (Mod.derivedExtendScalarsCompIso φ ψ χ h) (module_tower_on_homotopy φ ψ χ h)

end ModuleTower

set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem scalar_tower_monoidal (X : Scheme.{u})
    {R S T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ S) [IsMonHom a] (b : S ⟶ T) [IsMonHom b] :
    letI := scalarMonoidal X a
    letI := scalarMonoidal X b
    letI := scalarMonoidal X (a ≫ b)
    NatTrans.IsMonoidal (scalarTower X a b).hom := by
  delta scalarMonoidal scalar
  rw [scalar_monoidal_eq X a, scalar_monoidal_eq X b, scalar_monoidal_eq X (a ≫ b)]
  exact module_tower_monoidal (coefficientMap a X) (coefficientMap b X)
    (coefficientMap (a ≫ b) X) (coefficientMap_comp a b X).symm

private theorem mapMod_pull_preservesFlat
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj R Y)).PreservesFlat where
  flat_obj {M} hM := by
    rw [← CochainComplex.kFlat_single_obj_iff_flat _ 0] at hM ⊢
    exact ObjectProperty.prop_of_iso _
      ((HomologicalComplex.singleMapHomologicalComplex
        ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj R Y)) (.up ℤ) 0).app M)
      (Functor.kFlat_mapHomologicalComplex_obj _ _ hM)

set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem scalar_pull_on_homotopy
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) (.up ℤ)) :
    (CondensedRing.derivedUpperStarExtendScalarsIso a f).hom.app
        (DerivedCategory.Qh.obj P) ≫
      (CondensedRing.upperStar S f).leftDerivedFunctor.map
        ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app P) ≫
      (CondensedRing.upperStar S f).leftDerivedFunctorCounit.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (.up ℤ)).obj P) =
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
        ((CondensedRing.upperStar R f).leftDerivedFunctorCounit.app P) ≫
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
        (((CondensedRing.upperStar R f).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).hom (.up ℤ)).app P) := by
  let M := (f)^*[Ab.{u + 1}].mapMod (condensedRingObj R Y)
  letI : M.PreservesFlat := mapMod_pull_preservesFlat R f
  letI : M.IsLeftAdjoint :=
    ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
      (condensedRingObj R Y)).isLeftAdjoint
  let φ := condensedPullbackHom R f
  let ψ := coefficientMap a X
  let N := Mod.extendScalars φ
  let A := Mod.extendScalars ψ
  let B := Mod.extendScalars (φ ≫ ψ)
  let J := Mod.extendScalars (coefficientMap a Y)
  let K := CondensedRing.upperStar S f
  letI := Mod.extendScalarsMonoidal φ
  letI := Mod.extendScalarsMonoidal ψ
  letI := Mod.extendScalarsMonoidal (φ ≫ ψ)
  letI := Mod.extendScalarsMonoidal (coefficientMap a Y)
  let σ := Functor.leftDerivedFunctorCompMapDerivedCategoryIso M N
  let σB := Functor.leftDerivedFunctorCompMapDerivedCategoryIso M B
  let τ := Mod.derivedExtendScalarsCompIso φ ψ (φ ≫ ψ) rfl
  let θ := homotopy_comp_iso N A B (module_ordinary_tower φ ψ (φ ≫ ψ) rfl)
  let e := CondensedRing.mapModUpperStarExtendScalarsIso a f
  let ξ := Functor.leftDerivedFunctorIsoOfIso e
  let MP := (M.mapHomotopyCategory (.up ℤ)).obj P
  have hγ := right_exact_comparison_counit J K P
  simp only [right_exact_comparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc] at hγ
  have hσ := mixed_left_counit M N P
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hσ
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hσ
  have hσB := mixed_left_counit M B P
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hσB
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hσB
  have hiB : σB.inv.app (DerivedCategory.Qh.obj P) ≫
      (M ⋙ B).leftDerivedFunctorCounit.app P =
      B.leftDerivedFunctor.map (M.mapDerivedCategoryFactorsh.hom.app P) ≫
        B.leftDerivedFunctorCounit.app MP := by
    apply (cancel_epi (σB.hom.app (DerivedCategory.Qh.obj P))).1
    rw [Iso.hom_inv_id_app_assoc]
    exact hσB.symm
  have ht := module_tower_on_homotopy φ ψ (φ ≫ ψ) rfl MP
  have hiτ : τ.inv.app (DerivedCategory.Qh.obj MP) ≫
      B.leftDerivedFunctorCounit.app MP =
      A.leftDerivedFunctor.map (N.leftDerivedFunctorCounit.app MP) ≫
        A.leftDerivedFunctorCounit.app ((N.mapHomotopyCategory (.up ℤ)).obj MP) ≫
          DerivedCategory.Qh.map (θ.inv.app MP) := by
    have h := invert_normalization (τ.app (DerivedCategory.Qh.obj MP))
      ((composite_counit N A).app MP) (B.leftDerivedFunctorCounit.app MP)
      (DerivedCategory.Qh.mapIso (θ.app MP)) ht
    change τ.inv.app _ ≫ _ = (composite_counit N A).app MP ≫
      DerivedCategory.Qh.map (θ.inv.app MP) at h
    rw [composite_counit_app] at h
    simpa only [Category.assoc] using h
  have hθ : θ.inv.app MP ≫ (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P =
      (NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).hom (.up ℤ)).app P := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    dsimp only [MP, θ, homotopy_comp_iso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
    rw [module_ordinary_tower_comp]
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp]
    dsimp only [e, CondensedRing.mapModUpperStarExtendScalarsIso, Iso.trans_hom,
      Iso.symm_hom, Functor.isoWhiskerLeft_hom]
    rw [NatTrans.mapHomotopyCategory_comp, NatTrans.mapHomotopyCategory_comp]
    simp only [NatTrans.comp_app, map_homotopy_whisker_left,
      map_homotopy_associator_inv, Category.id_comp]
    rw [← Category.assoc, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
      Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
    erw [Category.id_comp]
  simp only [CondensedRing.derivedUpperStarExtendScalarsIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Iso.symm_hom, Category.id_comp, Category.assoc]
  change A.leftDerivedFunctor.map (σ.hom.app (DerivedCategory.Qh.obj P)) ≫
      τ.inv.app (M.mapDerivedCategory.obj (DerivedCategory.Qh.obj P)) ≫
      σB.inv.app (DerivedCategory.Qh.obj P) ≫ ξ.hom.app (DerivedCategory.Qh.obj P) ≫
      (Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso J K).hom.app
        (DerivedCategory.Qh.obj P) ≫
      K.leftDerivedFunctorIsoMapDerivedCategory.inv.app
        (J.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P)) ≫
      K.leftDerivedFunctor.map (J.leftDerivedFunctorCounit.app P) ≫
      K.leftDerivedFunctorCounit.app ((J.mapHomotopyCategory (.up ℤ)).obj P) = _
  rw [hγ, iso_counit]
  erw [reassoc_of% hiB]
  erw [← τ.inv.naturality_assoc]
  erw [reassoc_of% hiτ]
  simp only [Functor.comp_map]
  rw [← A.leftDerivedFunctor.map_comp_assoc, ← A.leftDerivedFunctor.map_comp_assoc]
  rw [Category.assoc]
  erw [hσ]
  erw [← DerivedCategory.Qh.map_comp, hθ]
  rfl

private theorem ordinary_identity_monoidal (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    letI := CondensedRing.internalScalarMonoidal (𝟙 R) X
    NatTrans.IsMonoidal ((Mod.extendRestrictAdjunction (coefficientMap (𝟙 R) X)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight
        (Mod.comapCongr (coefficientMap_id X) ≪≫
          Mod.comapId (condensedRingObj R X)).symm)).hom := by
  rw [scalar_monoidal_eq]
  let φ := coefficientMap (𝟙 R) X
  let r : Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientMap (𝟙 R) X) ≅
      𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) :=
    Mod.comapCongr (coefficientMap_id X) ≪≫ Mod.comapId (condensedRingObj R X)
  letI := Mod.comapLaxMonoidal φ
  letI := Mod.comapLaxMonoidal (𝟙 (condensedRingObj R X))
  letI := Mod.extendScalarsMonoidal φ
  haveI : NatTrans.IsMonoidal (Mod.comapId (condensedRingObj R X)).hom := by
    constructor
    · apply Mod.hom_ext
      simp only [Mod.comp_hom', Mod.comapId_hom_app_hom,
        Functor.LaxMonoidal.id_ε]
      rfl
    · intro M N
      apply Mod.hom_ext
      apply (cancel_epi (Mod.tensorObjπ
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (𝟙 (condensedRingObj R X))).obj M)
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (𝟙 (condensedRingObj R X))).obj N))).1
      simp only [Mod.comp_hom', Functor.LaxMonoidal.id_μ, Category.comp_id]
      change Mod.tensorObjπ _ _ ≫ (Mod.comapTensorHom _ M N).hom ≫
          ((Mod.comapId _).hom.app (M ⊗ N)).hom = _
      rw [Mod.tensorObjπ_comapTensorHom_hom_assoc]
      erw [Mod.tensorObjπ_tensorHom_hom_whisker]
      simp only [Mod.comapId_hom_app_hom]
      erw [id_whiskerRight, MonoidalCategory.whiskerLeft_id,
        Category.id_comp, Category.id_comp, Category.comp_id]
      rfl
  haveI : NatTrans.IsMonoidal
      (Mod.comapCongr (coefficientMap_id (Λ := R) X) :
        Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ ≅
          Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (𝟙 (condensedRingObj R X))).hom :=
    Mod.isMonoidal_comapCongr_hom (coefficientMap_id (Λ := R) X)
  haveI : NatTrans.IsMonoidal r.hom := by
    dsimp only [r, Iso.trans_hom]
    infer_instance
  haveI : NatTrans.IsMonoidal r.symm.hom := by
    change NatTrans.IsMonoidal r.inv
    infer_instance
  haveI := Mod.isMonoidal_extendRestrictAdjunction φ
  haveI := Adjunction.isMonoidal_ofNatIsoRight Adjunction.id r.symm
  exact Adjunction.isMonoidal_leftAdjointUniq_hom _ _

set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem scalar_identity_on_homotopy (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (P : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) (.up ℤ)) :
    let E := Mod.extendScalars (coefficientMap (𝟙 R) X)
    let r : Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientMap (𝟙 R) X) ≅
        𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) :=
      Mod.comapCongr (coefficientMap_id X) ≪≫ Mod.comapId (condensedRingObj R X)
    let e := (Mod.extendRestrictAdjunction (coefficientMap (𝟙 R) X)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight r.symm)
    (scalarIdentity X R).hom.app (DerivedCategory.Qh.obj P) =
      E.leftDerivedFunctorCounit.app P ≫
        DerivedCategory.Qh.map ((homotopy_iso_id E e).hom.app P) := by
  dsimp only
  let φ := coefficientMap (𝟙 R) X
  let E := Mod.extendScalars φ
  let U : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X) := Mod.comap φ
  let a := Mod.extendRestrictAdjunction φ
  let r : Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientMap (𝟙 R) X) ≅
      𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) :=
    Mod.comapCongr (coefficientMap_id X) ≪≫ Mod.comapId (condensedRingObj R X)
  let d := Functor.mapDerivedCategoryNatIso r ≪≫ Functor.mapDerivedCategoryIdIso _
  let e := a.leftAdjointUniq (Adjunction.id.ofNatIsoRight r.symm)
  have hr : d.inv.app (DerivedCategory.Qh.obj P) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory r.inv (.up ℤ)).app P) ≫
        U.mapDerivedCategoryFactorsh.inv.app P := by
    apply (cancel_mono (U.mapDerivedCategoryFactorsh.hom.app P)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have h := Adjunction.mapDerivedCategoryNatIso_trans_idIso_inv_app_Qh_obj r P
    convert h using 1 ; first | rfl | exact Category.comp_id _
  change ((Mod.derivedExtendMapDerivedCategoryAdjunction φ).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight d.symm)).hom.app _ = _
  rw [left_identity_hom, hr, E.leftDerivedFunctor.map_comp, Category.assoc,
    Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh]
  erw [E.leftDerivedFunctorCounit.naturality_assoc]
  have hm : (E.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory r.inv (.up ℤ)).app P) ≫
        (a.mapHomotopyCategory (.up ℤ)).counit.app P =
      (homotopy_iso_id E e).hom.app P := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient, homotopy_iso_id_quotient]
    change (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map _ = _
    rw [← (HomotopyCategory.quotient _ (.up ℤ)).map_comp]
    congr 1
    apply HomologicalComplex.hom_ext
    intro n
    simp only [Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_counit_app_f,
      cochain_iso_id, Iso.trans_hom, NatTrans.comp_app,
      NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexIdIso_hom_app_f]
    have h := (left_identity_hom a r (P.X n)).symm
    convert h using 1 <;> rfl
  have h := congrArg (fun f ↦ E.leftDerivedFunctorCounit.app P ≫ DerivedCategory.Qh.map f) hm
  simp only [DerivedCategory.Qh.map_comp] at h
  convert h using 1 ; rfl

private theorem scalar_identity_monoidal (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    letI := scalarMonoidal X (𝟙 R)
    NatTrans.IsMonoidal (scalarIdentity X R).hom := by
  letI := CondensedRing.internalScalarMonoidal (𝟙 R) X
  let e := (Mod.extendRestrictAdjunction (coefficientMap (𝟙 R) X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (Mod.comapCongr (coefficientMap_id X) ≪≫ Mod.comapId (condensedRingObj R X)).symm)
  haveI : NatTrans.IsMonoidal e.hom := ordinary_identity_monoidal X R
  exact derived_id_monoidal (Mod.extendScalars (coefficientMap (𝟙 R) X)) e
    (scalarIdentity X R) (scalar_identity_on_homotopy X R)

private theorem pull_monoidal_eq (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.monoidal_leftDerivedUpperStar R f =
      (CondensedRing.upperStar R f).leftDerivedFunctorMonoidal := by
  apply monoidal_eq_of_delta
  intro K L
  change ((CondensedRing.leftDerivedUpperStarTensor R f).app K).app L = _
  rw [Functor.leftDerivedFunctorMonoidal_δ,
    CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]

set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem scalar_pull_monoidal (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {Y : Scheme.{u}} (e : X ≅ Y) :
    letI := scalarMonoidal X a
    letI := scalarMonoidal Y a
    NatTrans.IsMonoidal (pullScalar X a e).hom := by
  letI := Mod.extendScalarsMonoidal (coefficientMap a X)
  letI := Mod.extendScalarsMonoidal (coefficientMap a Y)
  haveI := CondensedRing.isMonoidal_pullIso_hom a e.hom
  have h := derived_square_monoidal
    (CondensedRing.upperStar R e.hom) (Mod.extendScalars (coefficientMap a X))
    (Mod.extendScalars (coefficientMap a Y)) (CondensedRing.upperStar S e.hom)
    (CondensedRing.pullIso a e.hom) (CondensedRing.derivedUpperStarExtendScalarsIso a e.hom)
    (fun P ↦ by
      have hp := scalar_pull_on_homotopy a e.hom P
      simpa only [composite_counit_app, homotopy_square_iso, homotopy_comp_iso,
        Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
        Functor.mapHomotopyCategoryCompIso_refl_hom_app,
        Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.id_comp, Category.comp_id,
        NatTrans.mapHomotopyCategory_id, Iso.refl_hom, NatTrans.id_app, Category.assoc] using hp)
  delta scalarMonoidal scalar pullScalar
  rw [scalar_monoidal_eq X a, scalar_monoidal_eq Y a,
    pull_monoidal_eq R e.hom, pull_monoidal_eq S e.hom]
  exact h

private theorem comparison_eq (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (K L : D X R) :
    letI := scalarMonoidal X a
    comparison X a K L =
      (Functor.LaxMonoidal.ihomComparison (scalar X a) K).natTrans.app L := by
  letI := scalarMonoidal X a
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry]
  rfl

attribute [local irreducible] DerivedCategory.monoidalClosed
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution Mod.monoidalClosed

set_option maxHeartbeats 1500000 in
-- Derived comparison maps require substantial instance synthesis.
private theorem scalar_shift_coherence (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] : ShiftCoherence X a := by
  letI := CondensedRing.internalScalarMonoidal a X
  letI := scalarMonoidal X a
  constructor
  · intro K L n
    let F := scalar X a
    letI := (ihom.adjunction K).rightAdjointCommShift ℤ
    letI := (ihom.adjunction (F.obj K)).rightAdjointCommShift ℤ
    haveI := (ihom.adjunction K).commShift_of_leftAdjoint ℤ
    haveI := (ihom.adjunction (F.obj K)).commShift_of_leftAdjoint ℤ
    let δ : tensorLeft K ⋙ F ⟶ F ⋙ tensorLeft (F.obj K) :=
      (Mod.extendScalars (coefficientMap a X)).leftDerivedTensorComparison.app K
    haveI : NatTrans.CommShift δ ℤ :=
      tensor_left_shift (Mod.extendScalars (coefficientMap a X))
        (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientMap a X))
        (Mod.extendRestrictAdjunction (coefficientMap a X)) K
    haveI hμ : NatTrans.CommShift (Functor.LaxMonoidal.μTwoSquare F K).natTrans ℤ := by
      have he : (Functor.LaxMonoidal.μTwoSquare F K).natTrans = (asIso δ).inv := by
        apply (cancel_mono δ).1
        ext M
        simp only [δ, NatTrans.comp_app, Functor.LaxMonoidal.μTwoSquare,
          TwoSquare.natTrans, asIso_inv, IsIso.inv_hom_id, NatTrans.id_app]
        exact Functor.Monoidal.μ_δ F K M
      rw [he]
      haveI : NatTrans.CommShift (asIso δ).hom ℤ := ‹NatTrans.CommShift δ ℤ›
      exact NatTrans.CommShift.of_iso_inv (asIso δ) ℤ
    haveI : NatTrans.CommShift (Functor.LaxMonoidal.ihomComparison F K).natTrans ℤ :=
      NatTrans.CommShift.mateEquiv (A := ℤ)
        (ihom.adjunction K) (ihom.adjunction (F.obj K))
        (Functor.LaxMonoidal.μTwoSquare F K)
    simp only [comparison_eq, targetShift, Iso.app_hom]
    have h := NatTrans.shift_app_comm (Functor.LaxMonoidal.ihomComparison F K).natTrans n L
    simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at h
    convert h using 1 ; rfl
  · intro K L n
    haveI := (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a X)).left_adjoint_additive
    have h := opposite_source_shift_comparison
      (Mod.extendScalars (coefficientMap a X))
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientMap a X))
      (Mod.extendRestrictAdjunction (coefficientMap a X)) K L n
    simp only [comparison_eq, siteHomSignedSourceComponent,
      Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul]
    convert congrArg (fun f ↦ (n * (n + 1) / 2).negOnePow • f) h using 1 <;> rfl


/-- Shift, unit, tower and geometric interchange normalizations of the specified native
scalar functors and tensorators, before taking internal-Hom mates.
Source: Stacks 07A4, 08J9, 0D6D, 0FPT; Steps 9--11 of the item.
Proof: precompose the ordinary tensor diagrams with scalar units and tensor
coequalizer maps. The insertion-of-one equations and the uniqueness of normalized
scalar monoidal structures identify identity and composite scalar extension.
The same calculation with the canonical geometric inverse-image unit identifies
its scalar interchange, for every scheme isomorphism. On K-flat representatives
the derived tensorators compute these same ordinary tensorators. The canonical
exact derived scalar restriction and the left-adjoint uniqueness maps have the
corresponding unit equations. Transposing them identifies the chosen native
identity, scalar tower and pullback interchange with the computed comparisons.
Cancel the K-flat representative isomorphisms to obtain the three monoidality
assertions, including unit maps. This argument uses extension preserving K-flatness,
not flatness of the coefficient map. The normalized derived tensorator commutes
with shifts in both inputs on total complexes. Scalar shift is its mate under
exact restriction; target-Hom shift is the right-adjoint mate of tensor shift.
Taking mates of the tensor-shift square gives the target shift equation. For the
opposite source shift, use the same square with the parameter shift; the prescribed
factor (-1)^(n(n+1)/2) occurs on both sides. Additivity preserves it, so cancellation
gives the signed source equation for every integer. Identity maps, empty schemes,
zero complexes and negative shifts are covered by the same unit and mate laws.
(blueprint: lem-per-coefficient-hom-scalar-normalization). -/
theorem coefficient_hom_scalar_normalization (X : Scheme.{u}) :
    (∀ (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
      (a : R ⟶ S) [IsMonHom a], ShiftCoherence X a) ∧
    (∀ (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R],
      letI := scalarMonoidal X (𝟙 R)
      NatTrans.IsMonoidal (scalarIdentity X R).hom) ∧
    (∀ (R S T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
      [MonObj T] [IsCommMonObj T] (a : R ⟶ S) [IsMonHom a]
      (b : S ⟶ T) [IsMonHom b],
      letI := scalarMonoidal X a
      letI := scalarMonoidal X b
      letI := scalarMonoidal X (a ≫ b)
      NatTrans.IsMonoidal (scalarTower X a b).hom) ∧
    (∀ (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
      (a : R ⟶ S) [IsMonHom a] (Y : Scheme.{u}) (e : X ≅ Y),
      letI := scalarMonoidal X a
      letI := scalarMonoidal Y a
      NatTrans.IsMonoidal (pullScalar X a e).hom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R S _ _ _ _ a _
    exact scalar_shift_coherence X a
  · intro R _ _
    exact scalar_identity_monoidal X R
  · intro R S T _ _ _ _ _ _ a _ b _
    exact scalar_tower_monoidal X a b
  · intro R S _ _ _ _ a _ Y e
    exact scalar_pull_monoidal X a e

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
