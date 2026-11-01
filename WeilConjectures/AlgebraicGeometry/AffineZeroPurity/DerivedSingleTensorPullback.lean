/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import all WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import all Mathlib.Algebra.Homology.HomotopyCategory
import all Mathlib.Algebra.Homology.Monoidal
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Exact pullback and naturality of the degree-zero derived tensor pairing -/

@[expose] public noncomputable section
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] CategoryTheory.DerivedMonoidal HomotopyCategory
  CochainComplex.singleFunctor
  CochainComplex.singleFunctors CategoryTheory.Functor.mapHomotopyCategory
  HomologicalComplex.monoidalCategory HomologicalComplex.monoidalCategoryStruct
  HomotopyCategory.quotient CategoryTheory.Quotient.functor
  HomotopyCategory.MonoidalCategory.bifunctor
  CategoryTheory.Functor.bifunctorMapHomotopyCategory
  CategoryTheory.Quotient.lift CategoryTheory.Quotient.lift₂
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  CategoryTheory.SingleFunctors.postcomp
  CategoryTheory.Functor.map₂HomologicalComplex
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
attribute [local instance] SymmetricCategory.toBraidedCategory
section
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

private def singleQh (L : C) : (DerivedCategory.singleFunctor C 0).obj L ≅
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj L)) :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).app L ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app _

set_option maxHeartbeats 2000000 in
-- Canonical localization comparisons require additional elaboration work.
private theorem cupSingleTensorMap_factorization (L M : C) :
    let q := HomotopyCategory.quotient C (.up ℤ)
    let s := HomologicalComplex.single C (.up ℤ) 0
    cupSingleTensorMap L M =
      ((singleQh L).hom ⊗ₘ (singleQh M).hom) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj (s.obj L)) (q.obj (s.obj M)) ≫
        DerivedCategory.Qh.map (q.map (Etale.singleCochainTensorIso L M).hom) ≫
        (singleQh (L ⊗ M)).inv := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso C
  have hQ (K M : CochainComplex C ℤ) :
      Functor.LaxMonoidal.μ DerivedCategory.Q K M =
        (e.inv.app K ⊗ₘ e.inv.app M) ≫
          Functor.LaxMonoidal.μ (q ⋙ DerivedCategory.Qh) K M ≫ e.hom.app (K ⊗ M) := rfl
  dsimp only
  let s := HomologicalComplex.single C (.up ℤ) 0
  with_unfolding_all change (((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app L ⊗ₘ
      (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app M) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q (s.obj L) (s.obj M) ≫
      DerivedCategory.Q.map (Etale.singleCochainTensorIso L M).hom ≫
      (DerivedCategory.singleFunctorIsoCompQ C 0).inv.app (L ⊗ M)) = _
  erw [hQ]
  simp only [Functor.LaxMonoidal.comp_μ, Category.assoc]
  erw [← reassoc_of% e.hom.naturality (Etale.singleCochainTensorIso L M).hom]
  simp only [singleQh, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Iso.symm_hom, Iso.symm_inv,
    CochainComplex.singleFunctor, Functor.comp_obj]
  dsimp only [e, q, s]
  simp only [CochainComplex.singleFunctors]
  rw [← tensorHom_comp_tensorHom_assoc]
  congr 2
  apply congrArg (fun f ↦ Functor.LaxMonoidal.μ DerivedCategory.Qh
    (q.obj (s.obj L)) (q.obj (s.obj M)) ≫ f)
  change DerivedCategory.Qh.map (𝟙 _) ≫ _ = _
  exact (congrArg (fun f ↦ f ≫ _) (DerivedCategory.Qh.map_id _)).trans
    (Category.id_comp _)

variable {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]

omit [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
  [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D] in
private theorem singleQh_pullback (U : C ⥤ D) [U.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits U]
    [CategoryTheory.Limits.PreservesFiniteColimits U] (L : C) :
    U.leftDerivedFunctor.map (singleQh L).hom ≫
      U.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj
          ((HomologicalComplex.single C (.up ℤ) 0).obj L)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app L)) =
      U.singleFunctorCompLeftDerivedFunctorIso.hom.app L ≫
        (singleQh (U.obj L)).hom := by
  erw [← Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  erw [reassoc_of% U.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (singleQh L).hom]
  simp only [Functor.comp_obj, singleQh, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.map_comp, Functor.mapHomotopyCategory_obj,
    Functor.mapDerivedCategoryFactorsh_hom_app, DerivedCategory.Q_obj_single_obj,
    Category.assoc, Functor.singleFunctorCompLeftDerivedFunctorIso,
    Functor.mapDerivedCategorySingleFunctor, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, NatIso.cancel_natIso_hom_left]
  erw [Iso.map_inv_hom_id_assoc]
  simp only [Functor.mapHomotopyCategoryFactors, CategoryTheory.Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  try simp only [Category.assoc]
  erw [Category.id_comp, Category.assoc, Category.id_comp]
  let a := U.mapDerivedCategoryFactors.hom.app
    ((HomologicalComplex.single C (.up ℤ) 0).obj L)
  let c := (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app L
  with_unfolding_all change
    a ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map c) =
      a ≫ DerivedCategory.Q.map c ≫ 𝟙 _ ≫ 𝟙 _
  erw [Category.comp_id, Category.comp_id]
  with_unfolding_all rfl

omit [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
  [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C] in
private theorem singleQh_naturality {L M : C} (f : L ⟶ M) :
    (DerivedCategory.singleFunctor C 0).map f ≫ (singleQh M).hom =
      (singleQh L).hom ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (.up ℤ)).map
          ((HomologicalComplex.single C (.up ℤ) 0).map f)) :=
  (DerivedCategory.singleFunctorIsoCompQ C 0 ≪≫ Functor.isoWhiskerLeft _
    (DerivedCategory.quotientCompQhIso C).symm).hom.naturality f

set_option maxHeartbeats 2000000 in
-- Canonical localization comparisons require additional elaboration work.
/-- Naturality of the specified degree-zero derived tensor map.
Source: degree-(0,0) tensor comparison, Stacks Tag 06YU
(blueprint: lem-pur-derived-single-tensor-pullback).
Proof: compose the monoidal single-complex functor with Q and transport its lax
monoidal structure across singleFunctorIsoCompQ. Its tensorator is exactly the
specified map, so its naturality law is the required equation. -/
theorem cupSingleTensorMap_naturality
    {L L' M M' : C} (f : L ⟶ L') (g : M ⟶ M') :
    ((DerivedCategory.singleFunctor C 0).map f ⊗ₘ
        (DerivedCategory.singleFunctor C 0).map g) ≫ cupSingleTensorMap L' M' =
      cupSingleTensorMap L M ≫ (DerivedCategory.singleFunctor C 0).map (f ⊗ₘ g) := by
  obtain ⟨ms, hms⟩ := Etale.exists_singleCochainMonoidal (C := C)
  let := ms
  let e : DerivedCategory.singleFunctor C 0 ≅
      HomologicalComplex.single C (.up ℤ) 0 ⋙ DerivedCategory.Q :=
    DerivedCategory.singleFunctorIsoCompQ C 0
  let := Functor.LaxMonoidal.transport e.symm
  have fac (A B : C) : cupSingleTensorMap A B =
      Functor.LaxMonoidal.μ (DerivedCategory.singleFunctor C 0) A B := by
    rw [Functor.LaxMonoidal.transport_μ e.symm]
    simp only [Functor.LaxMonoidal.comp_μ, hms]
    simp only [cupSingleTensorMap, MonoidalCategory.tensorIso_hom,
      Etale.singleCochainTensorIso, e, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Category.assoc]
    rfl
  rw [fac, fac]
  exact Functor.LaxMonoidal.μ_natural _ f g

set_option maxHeartbeats 2000000 in
-- Canonical localization comparisons require additional elaboration work.
/-- Exact pullback preserves the specified degree-zero derived tensor map.
Source: degree-(0,0) tensor/counit calculation, Stacks Tags 06YQ and 06YU
(blueprint: lem-pur-derived-single-tensor-pullback).
Proof: factor the map through the single/Qh comparisons. The homotopy quotient
has identity tensorator. The termwise exact functor preserves the single-complex
tensorator, and its derived counit preserves the Qh tensorator. The canonical
exact single comparison factors through that counit. Transport the resulting
square through the three single/Qh comparisons and cancel their inverses. -/
theorem cupSingleTensorMap_pullback_of_counit (U : C ⥤ D) [U.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits U]
    [CategoryTheory.Limits.PreservesFiniteColimits U]
    [U.PreservesFlat] [U.IsLeftAdjoint] [U.Monoidal] (L M : C)
    (δ : Functor.leftDerivedDerivedTensor U ⟶ Functor.derivedTensorLeftDerived U)
    (hδ : ∀ X₁ X₂ : HomotopyCategory C (.up ℤ),
      (δ.app (DerivedCategory.Qh.obj X₁)).app (DerivedCategory.Qh.obj X₂) ≫
          (U.leftDerivedFunctorCounit.app X₁ ⊗ₘ U.leftDerivedFunctorCounit.app X₂) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Qh
            ((U.mapHomotopyCategory _).obj X₁) ((U.mapHomotopyCategory _).obj X₂) =
        U.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Qh X₁ X₂) ≫
          U.leftDerivedFunctorCounit.app (X₁ ⊗ X₂) ≫
          DerivedCategory.Qh.map
            (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) U).app X₁).app
              X₂)) :
    U.leftDerivedFunctor.map (cupSingleTensorMap L M) ≫
        U.singleFunctorCompLeftDerivedFunctorIso.hom.app (L ⊗ M) ≫
        (DerivedCategory.singleFunctor D 0).map (Functor.OplaxMonoidal.δ U L M) =
      ((δ.app
          ((DerivedCategory.singleFunctor C 0).obj L)).app
          ((DerivedCategory.singleFunctor C 0).obj M)) ≫
        (U.singleFunctorCompLeftDerivedFunctorIso.hom.app L ⊗ₘ
          U.singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
        cupSingleTensorMap (U.obj L) (U.obj M) := by
  let H := U.mapHomotopyCategory (.up ℤ)
  let F := U.leftDerivedFunctor
  let q := HomotopyCategory.quotient C (.up ℤ)
  let q' := HomotopyCategory.quotient D (.up ℤ)
  let s := HomologicalComplex.single C (.up ℤ) 0
  let s' := HomologicalComplex.single D (.up ℤ) 0
  let c := HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0
  erw [cupSingleTensorMap_factorization L M,
    cupSingleTensorMap_factorization (U.obj L) (U.obj M)]
  apply Etale.tensor_comparison_transport DerivedCategory.Qh DerivedCategory.Qh H F
    δ U.leftDerivedFunctorCounit
    (q.obj (s.obj L)) (q.obj (s.obj M)) (q.obj (s.obj (L ⊗ M)))
    (q'.obj (s'.obj (U.obj L))) (q'.obj (s'.obj (U.obj M)))
    (q'.obj (s'.obj (U.obj L ⊗ U.obj M)))
    (q.map (Etale.singleCochainTensorIso L M).hom)
    (q'.map (Etale.singleCochainTensorIso (U.obj L) (U.obj M)).hom)
    (q'.map (c.hom.app L)) (q'.map (c.hom.app M))
    (q'.map (c.hom.app (L ⊗ M)) ≫ q'.map (s'.map (Functor.OplaxMonoidal.δ U L M)))
    (Etale.singleHomotopyTensorIso_pullback U L M)
    (hδ _ _)
    (singleQh L) (singleQh M) (singleQh (L ⊗ M))
    (singleQh (U.obj L)) (singleQh (U.obj M)) (singleQh (U.obj L ⊗ U.obj M))
    (U.singleFunctorCompLeftDerivedFunctorIso.hom.app L)
    (U.singleFunctorCompLeftDerivedFunctorIso.hom.app M)
    (U.singleFunctorCompLeftDerivedFunctorIso.hom.app (L ⊗ M) ≫
      (DerivedCategory.singleFunctor D 0).map (Functor.OplaxMonoidal.δ U L M))
    (singleQh_pullback U L).symm (singleQh_pullback U M).symm
  erw [Category.assoc, singleQh_naturality, ← Category.assoc,
    ← singleQh_pullback U (L ⊗ M)]
  dsimp only [F, q, q', s, s', c]
  erw [DerivedCategory.Qh.map_comp]
  let a := U.leftDerivedFunctor.map (singleQh (L ⊗ M)).hom
  let b := U.leftDerivedFunctorCounit.app (q.obj (s.obj (L ⊗ M)))
  let c' := DerivedCategory.Qh.map (q'.map (c.hom.app (L ⊗ M)))
  let d := DerivedCategory.Qh.map (q'.map (s'.map (Functor.OplaxMonoidal.δ U L M)))
  exact (Category.assoc a (b ≫ c') d).trans
    (congrArg (fun t ↦ a ≫ t) (Category.assoc b c' d))

/-- The canonical derived tensor comparison satisfies the counit hypothesis.
Source: Stacks Tags 06YQ and 06YU (blueprint: lem-pur-derived-single-tensor-pullback).
Proof: apply the preceding transport calculation to the defining counit square
of the canonical left-derived tensor comparison. -/
theorem cupSingleTensorMap_pullback (U : C ⥤ D) [U.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits U]
    [CategoryTheory.Limits.PreservesFiniteColimits U]
    [U.PreservesFlat] [U.IsLeftAdjoint] [U.Monoidal] (L M : C) :
    U.leftDerivedFunctor.map (cupSingleTensorMap L M) ≫
        U.singleFunctorCompLeftDerivedFunctorIso.hom.app (L ⊗ M) ≫
        (DerivedCategory.singleFunctor D 0).map (Functor.OplaxMonoidal.δ U L M) =
      ((U.leftDerivedTensorComparison.app
          ((DerivedCategory.singleFunctor C 0).obj L)).app
          ((DerivedCategory.singleFunctor C 0).obj M)) ≫
        (U.singleFunctorCompLeftDerivedFunctorIso.hom.app L ⊗ₘ
          U.singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
        cupSingleTensorMap (U.obj L) (U.obj M) :=
  cupSingleTensorMap_pullback_of_counit U L M U.leftDerivedTensorComparison
    U.leftDerivedTensorComparison_app_app_comp_tensorHom
end
end AlgebraicGeometry.ProEtale.AffineZeroPurity
