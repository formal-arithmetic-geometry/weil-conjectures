/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Self-extensions of a two-term rank-one complex

Source: blueprint sk-lem-sf-determination, counterexample step 11
(blueprint: lem-sf-two-term-self-extension-hom).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

open CochainComplex.HomComplex

private theorem rankOne_map_ext {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (eM : M ≅ ModuleCat.of R R)
    (eN : N ≅ ModuleCat.of R R) {f g : M ⟶ N}
    (h : (eM.inv ≫ f ≫ eN.hom).hom 1 = (eM.inv ≫ g ≫ eN.hom).hom 1) : f = g := by
  have he : eM.inv ≫ f ≫ eN.hom = eM.inv ≫ g ≫ eN.hom := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext_ring h
  simpa using congrArg (fun k ↦ eM.hom ≫ k ≫ eN.inv) he

private def scalarEval {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R) :
    Cochain P P 1 →+ R where
  toFun := fun c ↦ (e₀.inv ≫ c.v 0 1 rfl ≫ e₁.hom).hom 1
  map_zero' := by simp
  map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp]

private theorem scalarEval_injective {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    [P.IsStrictlyGE 0] [P.IsStrictlyLE 1] : Function.Injective (scalarEval P e₀ e₁) := by
  intro c d h
  apply Cochain.ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = 1 := by omega
    subst q
    exact rankOne_map_ext e₀ e₁ h
  · by_cases hn : p < 0
    · exact (P.isZero_of_isStrictlyGE 0 p hn).eq_of_src _ _
    · exact (P.isZero_of_isStrictlyLE 1 q (by omega)).eq_of_tgt _ _

private noncomputable def scalarCochain {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    (r : R) : Cochain P P 1 :=
  Cochain.mk fun p q hpq ↦ if h : p = 0 then
    eqToHom (congrArg P.X h) ≫ e₀.hom ≫
      ModuleCat.ofHom (LinearMap.mulLeft R r) ≫ e₁.inv ≫
        eqToHom (congrArg P.X (show 1 = q by omega)) else 0

private theorem scalarEval_scalarCochain {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R) (r : R) :
    scalarEval P e₀ e₁ (scalarCochain P e₀ e₁ r) = r := by
  simp [scalarEval, scalarCochain]

private theorem cochain_two_zero {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    [P.IsStrictlyGE 0] [P.IsStrictlyLE 1] (c : Cochain P P 2) : c = 0 := by
  apply Cochain.ext
  intro p q hpq
  by_cases hp : p < 0
  · exact (P.isZero_of_isStrictlyGE 0 p hp).eq_of_src _ _
  · exact (P.isZero_of_isStrictlyLE 1 q (by omega)).eq_of_tgt _ _

private theorem scalarEval_boundary {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    (x : R) (hd : ∀ r : R, (e₀.inv ≫ P.d 0 1 ≫ e₁.hom).hom r = x * r)
    (c : Cochain P P 0) :
    scalarEval P e₀ e₁ (δ 0 1 c) = x *
      ((e₀.inv ≫ c.v 0 0 rfl ≫ e₀.hom).hom 1 -
        (e₁.inv ≫ c.v 1 1 rfl ≫ e₁.hom).hom 1) := by
  have hd' : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom (LinearMap.mulLeft R x) ≫ e₁.inv := by
    apply rankOne_map_ext e₀ e₁
    simpa using hd 1
  have hlin := (e₁.inv ≫ c.v 1 1 rfl ≫ e₁.hom).hom.map_smul x (1 : R)
  simp only [smul_eq_mul, mul_one] at hlin
  dsimp only [scalarEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [δ_v 0 1 rfl c 0 1 rfl 0 1 (by omega) rfl]
  simp only [show Int.negOnePow 1 = -1 by decide, Units.neg_smul, one_smul,
    Preadditive.comp_add, Preadditive.comp_neg, Preadditive.add_comp,
    Preadditive.neg_comp, ModuleCat.hom_add, ModuleCat.hom_neg, LinearMap.add_apply,
    LinearMap.neg_apply]
  rw [hd']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, LinearMap.mulLeft_apply]
  simp only [← sub_eq_add_neg]
  change x * (e₀.hom.hom ((c.v 0 0 rfl).hom (e₀.inv.hom 1))) -
    e₁.hom.hom ((c.v 1 1 rfl).hom (e₁.inv.hom (x * 1))) = _
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, mul_one] using
    (show x * (e₀.inv ≫ c.v 0 0 rfl ≫ e₀.hom).hom 1 -
      (e₁.inv ≫ c.v 1 1 rfl ≫ e₁.hom).hom x = _ by rw [hlin, mul_sub]; rfl)

private noncomputable def boundaryWitness {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (r : R) : Cochain P P 0 :=
  Cochain.ofHoms fun i ↦ if h : i = 0 then
    eqToHom (congrArg P.X h) ≫ e₀.hom ≫
      ModuleCat.ofHom (LinearMap.mulLeft R r) ≫ e₀.inv ≫
        eqToHom (congrArg P.X h.symm) else 0

private theorem scalarEval_boundaryWitness {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    (x : R) (hd : ∀ r : R, (e₀.inv ≫ P.d 0 1 ≫ e₁.hom).hom r = x * r)
    (r : R) : scalarEval P e₀ e₁ (δ 0 1 (boundaryWitness P e₀ r)) = x * r := by
  rw [scalarEval_boundary P e₀ e₁ x hd]
  simp [boundaryWitness]

private theorem mem_coboundaries_iff_scalar {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    [P.IsStrictlyGE 0] [P.IsStrictlyLE 1]
    (x : R) (hd : ∀ r : R, (e₀.inv ≫ P.d 0 1 ≫ e₁.hom).hom r = x * r)
    (c : Cocycle P P 1) :
    c ∈ coboundaries P P 1 ↔ scalarEval P e₀ e₁ c ∈ Ideal.span {x} := by
  rw [mem_coboundaries_iff c 0 rfl, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    rw [← hb, scalarEval_boundary P e₀ e₁ x hd]
    exact dvd_mul_right _ _
  · rintro ⟨r, hr⟩
    refine ⟨boundaryWitness P e₀ r, scalarEval_injective P e₀ e₁ ?_⟩
    rw [scalarEval_boundaryWitness P e₀ e₁ x hd, hr]

private noncomputable def scalarCocycle {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    [P.IsStrictlyGE 0] [P.IsStrictlyLE 1] (r : R) : Cocycle P P 1 :=
  Cocycle.mk (scalarCochain P e₀ e₁ r) 2 rfl (cochain_two_zero P _)

private def cocycleScalarQuotient {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    (x : R) : Cocycle P P 1 →+ R ⧸ Ideal.span {x} :=
  (Ideal.Quotient.mk (Ideal.span {x})).toAddMonoidHom.comp
    ((scalarEval P e₀ e₁).comp (cocycle P P 1).subtype)

private noncomputable def classScalarQuotient {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    [P.IsStrictlyGE 0] [P.IsStrictlyLE 1]
    (x : R) (hd : ∀ r : R, (e₀.inv ≫ P.d 0 1 ≫ e₁.hom).hom r = x * r) :
    CohomologyClass P P 1 →+ R ⧸ Ideal.span {x} :=
  CohomologyClass.descAddMonoidHom (cocycleScalarQuotient P e₀ e₁ x) (by
    intro c hc
    change Ideal.Quotient.mk _ (scalarEval P e₀ e₁ c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((mem_coboundaries_iff_scalar P e₀ e₁ x hd c).mp hc))

private theorem classScalarQuotient_bijective {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    [P.IsStrictlyGE 0] [P.IsStrictlyLE 1]
    (x : R) (hd : ∀ r : R, (e₀.inv ≫ P.d 0 1 ≫ e₁.hom).hom r = x * r) :
    Function.Bijective (classScalarQuotient P e₀ e₁ x hd) := by
  constructor
  · intro a b h
    have hz : classScalarQuotient P e₀ e₁ x hd (a - b) = 0 := by
      rw [map_sub, h, sub_self]
    rw [← sub_eq_zero]
    obtain ⟨c, hc⟩ := CohomologyClass.mk_surjective (a - b)
    rw [← hc] at hz ⊢
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff_scalar P e₀ e₁ x hd]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨CohomologyClass.mk (scalarCocycle P e₀ e₁ r), ?_⟩
    change Ideal.Quotient.mk _ (scalarEval P e₀ e₁ (scalarCochain P e₀ e₁ r)) = _
    rw [scalarEval_scalarCochain]

private noncomputable def classDerivedHomEquiv {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] :
    CohomologyClass P P 1 ≃+ (Q.obj P ⟶ (Q.obj P)⟦(1 : ℤ)⟧) :=
  (CohomologyClass.homAddEquiv (K := P) (L := P) (n := 1)).trans
    ((AddEquiv.ofBijective Qh.mapAddHom
      (CochainComplex.IsKProjective.Qh_map_bijective P _)).trans
        (CategoryTheory.Linear.homCongr ℤ ((quotientCompQhIso _).app P)
          ((quotientCompQhIso _).app (P⟦(1 : ℤ)⟧) ≪≫
            (Q.commShiftIso (1 : ℤ)).app P)).toAddEquiv)

private theorem classDerivedHomEquiv_mk {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective]
    (f : P ⟶ P⟦(1 : ℤ)⟧) :
    classDerivedHomEquiv P (CohomologyClass.mk (Cocycle.equivHomShift f)) =
      Q.map f ≫ (Q.commShiftIso (1 : ℤ)).hom.app P := by
  change ((quotientCompQhIso (ModuleCat R)).inv.app P ≫
    Qh.map (CohomologyClass.toHom (CohomologyClass.mk (Cocycle.equivHomShift f)))) ≫
      ((quotientCompQhIso (ModuleCat R)).hom.app (P⟦(1 : ℤ)⟧) ≫
        (Q.commShiftIso (1 : ℤ)).hom.app P) = _
  rw [Category.assoc]
  rw [CohomologyClass.toHom_mk, AddEquiv.symm_apply_apply]
  rw [← quotientCompQhIso_inv_naturality_assoc f]
  simp

/-- The degree-one derived endomorphisms of a two-term rank-one complex form the
coefficient quotient by its differential, normalized by evaluation at one.

Source: blueprint sk-lem-sf-determination, counterexample step 11
(blueprint: lem-sf-two-term-self-extension-hom).

Proof: Chain maps from `P` to `P[1]` are determined by the degree-zero component and
therefore by one scalar. Homotopies change that scalar by a multiple of `x`, so the
homotopy classes are the additive quotient by the principal ideal `(x)`. The bounded
projective source is K-projective, and the localization bijection transports this
additive equivalence to the derived category. -/
theorem exists_twoTerm_selfExtension_hom_equiv (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e₀ : P.X 0 ≅ ModuleCat.of R R) (e₁ : P.X 1 ≅ ModuleCat.of R R)
    (x : R) (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE 1)
    (hd : ∀ r : R, (e₀.inv ≫ P.d 0 1 ≫ e₁.hom).hom r = x * r) :
    ∃ e : (Q.obj P ⟶ (Q.obj P)⟦(1 : ℤ)⟧) ≃+ R ⧸ Ideal.span {x},
      ∀ f : P ⟶ P⟦(1 : ℤ)⟧,
        e (Q.map f ≫ (Q.commShiftIso (1 : ℤ)).hom.app P) =
          Ideal.Quotient.mk (Ideal.span {x})
            ((e₀.inv ≫ f.f 0 ≫ (P.shiftFunctorObjXIso (1 : ℤ) 0 1 rfl).hom ≫
              e₁.hom).hom 1) := by
  classical
  let := hge
  let := hle
  have (i : ℤ) : Projective (P.X i) := by
    by_cases h₀ : i = 0
    · subst i
      exact Projective.of_iso e₀.symm inferInstance
    · by_cases h₁ : i = 1
      · subst i
        exact Projective.of_iso e₁.symm inferInstance
      · by_cases hi : i < 0
        · exact (P.isZero_of_isStrictlyGE 0 i hi).projective
        · exact (P.isZero_of_isStrictlyLE 1 i (by omega)).projective
  have := CochainComplex.isKProjective_of_projective P 1
  let eC := AddEquiv.ofBijective (classScalarQuotient P e₀ e₁ x hd)
    (classScalarQuotient_bijective P e₀ e₁ x hd)
  let eD := classDerivedHomEquiv P
  refine ⟨eD.symm.trans eC, ?_⟩
  intro f
  rw [← classDerivedHomEquiv_mk P f]
  change eC (eD.symm (eD (CohomologyClass.mk (Cocycle.equivHomShift f)))) = _
  rw [eD.symm_apply_apply]
  change Ideal.Quotient.mk _
    (scalarEval P e₀ e₁ (Cocycle.equivHomShift f)) = _
  simp [scalarEval, Cocycle.equivHomShift_apply, Cocycle.rightUnshift,
    Cochain.rightUnshift, Cochain.ofHom]

end DerivedCategory
