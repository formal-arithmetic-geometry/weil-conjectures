/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Auxiliary transposition lemmas for the singleton scalar representative

Source: Stacks 0FND and 09T5 (blueprint: lem-pur-system-singleton-scalar-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

section Pointwise

variable {A : Type*} {B : Type*} {C : Type*} {DA : Type*} {DB : Type*} {DC : Type*}
  [Category A] [Category B] [Category C] [Category DA] [Category DB] [Category DC]
  {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
  {FD : DA ⥤ DB} {RD : DB ⥤ DA} {GD : DB ⥤ DC} {SD : DC ⥤ DB}
  {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}

/-- Pointwise version of `normalizedAdjunction_composition`: normalized transposes compose.
Source: Stacks 0FND (blueprint: lem-pur-system-singleton-scalar-representative). -/
theorem normalizedAdjunction_composition_pointwise
    (a : F ⊣ R) (b : G ⊣ S) (ad : FD ⊣ RD) (bd : GD ⊣ SD)
    (εF : ∀ P, FD.obj (QA.obj P) ⟶ QB.obj (F.obj P))
    (εG : ∀ P, GD.obj (QB.obj P) ⟶ QC.obj (G.obj P))
    (ρF : ∀ K, QA.obj (R.obj K) ⟶ RD.obj (QB.obj K))
    (ρG : ∀ K, QB.obj (S.obj K) ⟶ SD.obj (QC.obj K))
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF K)
    (hG : ∀ P K (f : G.obj P ⟶ K),
      bd.homEquiv _ _ (εG P ≫ QC.map f) = QB.map (b.homEquiv _ _ f) ≫ ρG K)
    (P : A) (K : C) (f : G.obj (F.obj P) ⟶ K) :
    (ad.comp bd).homEquiv _ _ ((GD.map (εF P) ≫ εG (F.obj P)) ≫ QC.map f) =
      QA.map ((a.comp b).homEquiv _ _ f) ≫ ρF (S.obj K) ≫ RD.map (ρG K) := by
  rw [Category.assoc]
  simp only [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.trans_apply]
  erw [bd.homEquiv_naturality_left]
  rw [hG, ← Category.assoc, ad.homEquiv_naturality_right, hF, Category.assoc]
  rfl

end Pointwise

section DerivedEquivalence

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- Transposition across a composite adjunction with a transported right adjoint, in terms
of the transposes across the two factors. -/
theorem comp_ofNatIsoRight_homEquiv_eq {DA DB DC : Type*} [Category DA] [Category DB]
    [Category DC] {FD : DA ⥤ DB} {RD : DB ⥤ DA} {FE : DB ⥤ DC} {GE : DC ⥤ DB} {U : DC ⥤ DA}
    (ad : FD ⊣ RD) (eq : FE ⊣ GE) (δ : GE ⋙ RD ≅ U) {X : DA} {B₁ : DB} {Y₁ Y : DC}
    {B₂ : DB} {A₁ : DA} (x : FD.obj X ⟶ B₁) (p : FE.obj B₁ ⟶ Y₁) (y : Y₁ ⟶ Y)
    (g : B₁ ⟶ B₂) (s : B₂ ⟶ GE.obj Y) (t : X ⟶ A₁) (r : A₁ ⟶ RD.obj B₂) (w : A₁ ⟶ U.obj Y)
    (hE : eq.homEquiv B₁ Y (p ≫ y) = g ≫ s) (hA : ad.homEquiv X B₂ (x ≫ g) = t ≫ r)
    (hC : r ≫ RD.map s ≫ δ.hom.app Y = w) :
    ((ad.comp eq).ofNatIsoRight δ).homEquiv X Y ((FE.map x ≫ p) ≫ y) = t ≫ w := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  rw [Category.assoc]
  erw [eq.homEquiv_naturality_left]
  rw [hE, ← Category.assoc, ad.homEquiv_naturality_right, hA, Category.assoc, Category.assoc, hC]

/-- Inverting the outer factorization isomorphisms of a commutative square. -/
theorem iso_square_inv_eq {C' : Type*} [Category C'] {A₁ A₂ A₃ B₁ B₂ B₃ : C'}
    (u : A₁ ≅ A₂) (v : A₂ ≅ A₃) (x : B₁ ≅ B₂) (y : B₂ ≅ B₃) (S : A₁ ⟶ B₁) (q : A₃ ⟶ B₃)
    (h : S ≫ x.hom ≫ y.hom = u.hom ≫ v.hom ≫ q) :
    (v.inv ≫ u.inv) ≫ S = q ≫ y.inv ≫ x.inv := by
  calc (v.inv ≫ u.inv) ≫ S = (v.inv ≫ u.inv) ≫ (S ≫ x.hom ≫ y.hom) ≫ y.inv ≫ x.inv := by
        simp
    _ = q ≫ y.inv ≫ x.inv := by
        rw [h]
        simp

section Square

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F₁ : A ⥤ B) (F₂ : B ⥤ D) (F₃ : A ⥤ C) (F₄ : C ⥤ D)
  [F₁.Additive] [F₂.Additive] [F₃.Additive] [F₄.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
  [PreservesFiniteLimits F₄] [PreservesFiniteColimits F₄]

/-- The derived square of exact functors, written with the inverse factorization maps, is
the localization of the ordinary square.
Source: Stacks Tag 05S7 (blueprint: lem-pur-system-singleton-scalar-representative). -/
theorem Functor.mapDerivedCategorySquareIso_hom_app_inv_factors (σ : F₁ ⋙ F₂ ≅ F₃ ⋙ F₄)
    (K : CochainComplex A ℤ) :
    (F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app K)) ≫
      (Functor.mapDerivedCategorySquareIso σ).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app K) ≫
        F₄.mapDerivedCategoryFactors.inv.app ((F₃.mapHomologicalComplex (.up ℤ)).obj K) ≫
        F₄.mapDerivedCategory.map (F₃.mapDerivedCategoryFactors.inv.app K) := by
  refine iso_square_inv_eq (F₂.mapDerivedCategory.mapIso (F₁.mapDerivedCategoryFactors.app K))
    (F₂.mapDerivedCategoryFactors.app _) (F₄.mapDerivedCategory.mapIso
      (F₃.mapDerivedCategoryFactors.app K)) (F₄.mapDerivedCategoryFactors.app _) _ _ ?_
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Functor.mapIso_hom, Iso.app_hom]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ K]
  simp

end Square

/-- Inverting a factorization of an isomorphism through three isomorphisms. -/
theorem iso_chain_inv_eq {C' : Type*} [Category C'] {W X Y Z : C'}
    (a : W ≅ X) (b : X ≅ Y) (c : Y ≅ Z) (d : W ≅ Z)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom) : c.inv ≫ b.inv ≫ a.inv = d.inv := by
  rw [← cancel_mono d.hom, Iso.inv_hom_id, ← h]
  simp

/-- Inverting a factorization of an isomorphism through three isomorphisms. -/
theorem iso_chain_inv_comp_eq {C' : Type*} [Category C'] {W X Y Z U V : C'}
    (a : W ≅ X) (b : X ≅ Y) (c : Y ≅ Z) (d : W ≅ Z) (n : W ⟶ U) (i : U ⟶ V) (q : Z ⟶ V)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom) (h' : n ≫ i = d.hom ≫ q) :
    c.inv ≫ b.inv ≫ a.inv ≫ n ≫ i = q := by
  rw [h', ← h]
  simp

/-- Transport of a composite image along a factorization isomorphism. -/
theorem functor_map_comp_chain_eq {C' D' : Type*} [Category C'] [Category D'] (Φ : C' ⥤ D')
    {A B B' : C'} {P S V : D'} (x : A ⟶ B) (y : B ⟶ B') (k : Φ.obj B' ⟶ V)
    (p : Φ.obj A ⟶ P) (s : Φ.obj B ≅ S) (r : P ⟶ S) (w : S ⟶ V) (z : P ⟶ V)
    (hm : Φ.map x ≫ s.hom = p ≫ r) (hc : s.inv ≫ Φ.map y ≫ k = w) (hf : r ≫ w = z) :
    Φ.map (x ≫ y) ≫ k = p ≫ z := by
  rw [Φ.map_comp, ← hf, ← hc, ← reassoc_of% hm]
  simp

/-- The derived equivalence transposes a localized complex map to the localized termwise
transpose. Source: Stacks 05S7 (blueprint: lem-pur-system-singleton-scalar-representative).
Proof: the derived unit is the localized termwise unit by the identity, natural-isomorphism
and composition comparisons. -/
theorem Equivalence.mapDerivedCategory_homEquiv_Q (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    (X : CochainComplex C ℤ) (Y : CochainComplex D ℤ)
    (f : (e.functor.mapHomologicalComplex (.up ℤ)).obj X ⟶ Y) :
    e.mapDerivedCategory.toAdjunction.homEquiv _ _
        (e.functor.mapDerivedCategoryFactors.hom.app X ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
          ((e.toAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv X Y f) ≫
        e.inverse.mapDerivedCategoryFactors.inv.app Y := by
  have hc : e.functor.mapDerivedCategoryFactors.inv.app
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj Y) ≫
      e.functor.mapDerivedCategory.map (e.inverse.mapDerivedCategoryFactors.inv.app Y) ≫
      e.mapDerivedCategory.toAdjunction.counit.app (DerivedCategory.Q.obj Y) =
      DerivedCategory.Q.map ((e.toAdjunction.mapHomologicalComplex (.up ℤ)).counit.app Y) := by
    have h1 := Functor.mapDerivedCategoryCompIso_hom_app_factors e.inverse e.functor Y
    have h2 := Functor.mapDerivedCategoryNatIso_fac e.counitIso Y
    have h3 := Functor.mapDerivedCategoryIdIso_hom_app_Q_obj Y
    have hε : e.mapDerivedCategory.toAdjunction.counit.app (DerivedCategory.Q.obj Y) =
        (Functor.mapDerivedCategoryCompIso e.inverse e.functor).inv.app _ ≫
          (Functor.mapDerivedCategoryNatIso e.counitIso).hom.app _ ≫
          (Functor.mapDerivedCategoryIdIso D).hom.app _ := rfl
    have h2' : (Functor.mapDerivedCategoryNatIso e.counitIso).hom.app (DerivedCategory.Q.obj Y) ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app (DerivedCategory.Q.obj Y) =
        (e.inverse ⋙ e.functor).mapDerivedCategoryFactors.hom.app Y ≫
          DerivedCategory.Q.map ((e.toAdjunction.mapHomologicalComplex (.up ℤ)).counit.app Y) := by
      rw [h3]
      exact h2
    rw [hε]
    exact iso_chain_inv_comp_eq ((Functor.mapDerivedCategoryCompIso e.inverse e.functor).app _)
      (e.functor.mapDerivedCategory.mapIso (e.inverse.mapDerivedCategoryFactors.app Y))
      (e.functor.mapDerivedCategoryFactors.app _)
      ((e.inverse ⋙ e.functor).mapDerivedCategoryFactors.app Y) _ _ _ h1 h2'
  apply (e.mapDerivedCategory.toAdjunction.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  erw [Adjunction.homEquiv_counit]
  have hf : DerivedCategory.Q.map ((e.functor.mapHomologicalComplex (.up ℤ)).map
        ((e.toAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv X Y f)) ≫
      DerivedCategory.Q.map ((e.toAdjunction.mapHomologicalComplex (.up ℤ)).counit.app Y) =
      DerivedCategory.Q.map f := by
    rw [← Functor.map_comp]
    erw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  exact (functor_map_comp_chain_eq e.mapDerivedCategory.functor _ _ _ _
    (e.functor.mapDerivedCategoryFactors.app _) _ _ _
    (e.functor.mapDerivedCategoryFactors_hom_naturality _) hc hf).symm


end DerivedEquivalence

end CategoryTheory
