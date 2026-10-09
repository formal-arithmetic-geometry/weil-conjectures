/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DualNumbers.Lift

/-!
# Retractions of dual-number thickenings as operators on functions

A morphism `h : X[ε] ⟶ X` restricting to the identity along `ε ↦ 0` is the identity on points,
and acts on functions by `h^♯(a) = a + ε D(a)` for an additive operator `D` on the sections of
`𝒪_X` (`AlgebraicGeometry.Scheme.Hom.dualNumbersDeriv`). Similarly a morphism
`h : X[ε][δ] ⟶ X` restricting to the identity along `ε, δ ↦ 0` acts by
`h^♯(a) = a + ε D₁(a) + δ D₂(a) + εδ D₁₂(a)`; we record the operators as one element
`1 + ε D₁ + δ D₂ + εδ D₁₂` of the (noncommutative) ring of two-parameter dual numbers over the
endomorphisms of `Γ(X, U)` (`AlgebraicGeometry.Scheme.Hom.dualNumbers₂Op`).

If `Λ` is an endomorphism of the thickening fixing the infinitesimals, the operator of `Λ ≫ h₂` is
the product of the operators of `Λ ≫ p` and of `h₂`
(`AlgebraicGeometry.Scheme.Hom.dualNumbersDeriv_comp`,
`AlgebraicGeometry.Scheme.Hom.dualNumbers₂Op_comp`).
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt Opposite

namespace AlgebraicGeometry

private theorem addMonoidEnd_add_apply {A : Type*} [AddCommGroup A] (f g : AddMonoid.End A)
    (a : A) : (f + g) a = f a + g a :=
  rfl

namespace Scheme

variable {X : Scheme.{u}}

/-! ### One parameter -/

section One

variable {h : X.dualNumbers ⟶ X} (hh : X.dualNumbersι ≫ h = 𝟙 X)

include hh in
theorem le_preimage_self_of_dualNumbersι_comp_eq_id (U : X.Opens) : U ≤ h ⁻¹ᵁ U :=
  le_preimage_of_dualNumbersι_comp hh (U := U) le_rfl

include hh in
theorem fst_appLE_of_dualNumbersι_comp_eq_id (U : X.Opens) (e : U ≤ h ⁻¹ᵁ U) (a : Γ(X, U)) :
    (h.appLE U U e a).fst = a := by
  have := Hom.appLE_apply_eq_of_eq hh U U (le_preimage_of_dualNumbersι_comp hh (U := U) le_rfl)
    le_rfl a
  rw [Hom.appLE_comp_apply X.dualNumbersι h U U U e le_rfl, dualNumbersι_appLE,
    Hom.id_appLE_apply] at this
  exact (presheaf_map_self_apply X _ _).symm.trans (this.trans (presheaf_map_self_apply X _ _))

/-- The operator `D` on the sections of `𝒪_X` over `U` of a morphism `h : X[ε] ⟶ X` restricting
to the identity: `h^♯(a) = a + ε D(a)`. -/
noncomputable def Hom.dualNumbersDeriv (U : X.Opens) : AddMonoid.End Γ(X, U) where
  toFun a := (h.appLE U U (le_preimage_self_of_dualNumbersι_comp_eq_id hh U) a).snd
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add]; rfl

theorem Hom.dualNumbersDeriv_congr {h' : X.dualNumbers ⟶ X} (hh' : X.dualNumbersι ≫ h' = 𝟙 X)
    (e : h = h') (U : X.Opens) : Hom.dualNumbersDeriv hh U = Hom.dualNumbersDeriv hh' U := by
  subst e
  rfl

theorem Hom.dualNumbersDeriv_apply (U : X.Opens) (e : U ≤ h ⁻¹ᵁ U) (a : Γ(X, U)) :
    Hom.dualNumbersDeriv hh U a = (h.appLE U U e a).snd :=
  rfl

/-- If `Λ` is an endomorphism of `X[ε]` fixing `ε`, the operator of `Λ ≫ h₂` is the sum of the
operators of `Λ ≫ p` and of `h₂`: `(1 + ε D₁)(1 + ε D₂) = 1 + ε (D₁ + D₂)`. -/
theorem Hom.dualNumbersDeriv_comp (Λ : X.dualNumbers ⟶ X.dualNumbers)
    (hε : Λ.appTop (inr 1 : DualNumber Γ(X, ⊤)) = (inr 1 : DualNumber Γ(X, ⊤)))
    {h₁ h₂ : X.dualNumbers ⟶ X} (hΛ : Λ ≫ X.dualNumbersProj = h₁)
    (hh₁ : X.dualNumbersι ≫ h₁ = 𝟙 X) (hh₂ : X.dualNumbersι ≫ h₂ = 𝟙 X)
    (hh₃ : X.dualNumbersι ≫ Λ ≫ h₂ = 𝟙 X) (U : X.Opens) :
    Hom.dualNumbersDeriv hh₃ U = Hom.dualNumbersDeriv hh₁ U + Hom.dualNumbersDeriv hh₂ U := by
  ext a
  have e₁ := le_preimage_self_of_dualNumbersι_comp_eq_id hh₁ U
  have e₂ := le_preimage_self_of_dualNumbersι_comp_eq_id hh₂ U
  have eΛ : U ≤ Λ ⁻¹ᵁ U := le_preimage_of_comp_dualNumbersProj hΛ e₁
  have e' : U ≤ (Λ ≫ X.dualNumbersProj) ⁻¹ᵁ U := hΛ ▸ e₁
  rw [AddMonoidHom.add_apply, Hom.dualNumbersDeriv_apply hh₃ U
    (le_preimage_self_of_dualNumbersι_comp_eq_id hh₃ U), Hom.dualNumbersDeriv_apply hh₁ U e₁,
    Hom.dualNumbersDeriv_apply hh₂ U e₂, Hom.appLE_comp_apply Λ h₂ U U U e₂ eΛ,
    (appLE_dualNumbers_self Λ hε U eΛ e' _).2, Hom.appLE_apply_eq_of_eq hΛ U U e' e₁,
    Hom.appLE_apply_eq_of_eq hΛ U U e' e₁, fst_appLE_of_dualNumbersι_comp_eq_id hh₂ U e₂,
    fst_appLE_of_dualNumbersι_comp_eq_id hh₁ U e₁]

end One

theorem dualNumbersι_appLE_self (U : X.Opens) (e : U ≤ X.dualNumbersι ⁻¹ᵁ U)
    (x : Γ(X.dualNumbers, U)) : X.dualNumbersι.appLE U U e x = x.fst :=
  (dualNumbersι_appLE U U e x).trans (presheaf_map_self_apply X _ _)

/-! ### Two parameters -/

section Two

variable {h : X.dualNumbers.dualNumbers ⟶ X}
  (hh : X.dualNumbersι ≫ X.dualNumbers.dualNumbersι ≫ h = 𝟙 X)

include hh in
theorem le_preimage_self_of_dualNumbersι₂_comp_eq_id (U : X.Opens) : U ≤ h ⁻¹ᵁ U := by
  intro x hx
  have : x ∈ (𝟙 X) ⁻¹ᵁ U := hx
  rw [← hh] at this
  exact this

include hh in
theorem fst_fst_appLE_of_dualNumbersι₂_comp_eq_id (U : X.Opens) (e : U ≤ h ⁻¹ᵁ U)
    (a : Γ(X, U)) : (h.appLE U U e a).fst.fst = a := by
  have := Hom.appLE_apply_eq_of_eq hh U U (fun x hx ↦ e hx) le_rfl a
  rw [Hom.appLE_comp_apply X.dualNumbersι (X.dualNumbers.dualNumbersι ≫ h) U U U
    (le_preimage_of_dualNumbersι_comp (h := X.dualNumbers.dualNumbersι ≫ h) rfl e) le_rfl,
    Hom.appLE_comp_apply X.dualNumbers.dualNumbersι h U U U e le_rfl,
    dualNumbersι_appLE_self, dualNumbersι_appLE_self (X := X.dualNumbers),
    Hom.id_appLE_apply] at this
  exact this.trans (presheaf_map_self_apply X _ _)

/-- The operator `1 + ε D₁ + δ D₂ + εδ D₁₂` on the sections of `𝒪_X` over `U` of a morphism
`h : X[ε][δ] ⟶ X` restricting to the identity: `h^♯(a) = a + ε D₁(a) + δ D₂(a) + εδ D₁₂(a)`. -/
noncomputable def Hom.dualNumbers₂Op (U : X.Opens) :
    DualNumber (DualNumber (AddMonoid.End Γ(X, U))) :=
  let e := le_preimage_self_of_dualNumbersι₂_comp_eq_id hh U
  inl (inl 1 + inr
    { toFun a := (h.appLE U U e a).fst.snd
      map_zero' := by rw [map_zero]; rfl
      map_add' a b := by rw [map_add]; rfl }) +
  inr (inl
    { toFun a := (h.appLE U U e a).snd.fst
      map_zero' := by rw [map_zero]; rfl
      map_add' a b := by rw [map_add]; rfl } + inr
    { toFun a := (h.appLE U U e a).snd.snd
      map_zero' := by rw [map_zero]; rfl
      map_add' a b := by rw [map_add]; rfl })

theorem Hom.dualNumbers₂Op_congr {h' : X.dualNumbers.dualNumbers ⟶ X}
    (hh' : X.dualNumbersι ≫ X.dualNumbers.dualNumbersι ≫ h' = 𝟙 X) (e : h = h') (U : X.Opens) :
    Hom.dualNumbers₂Op hh U = Hom.dualNumbers₂Op hh' U := by
  subst e
  rfl

variable (U : X.Opens) (e : U ≤ h ⁻¹ᵁ U) (a : Γ(X, U))

@[simp]
theorem Hom.fst_fst_dualNumbers₂Op : (Hom.dualNumbers₂Op hh U).fst.fst = 1 := by
  simp [Hom.dualNumbers₂Op]

theorem Hom.fst_snd_dualNumbers₂Op_apply :
    (Hom.dualNumbers₂Op hh U).fst.snd a = (h.appLE U U e a).fst.snd := by
  simp [Hom.dualNumbers₂Op]
  rfl

theorem Hom.snd_fst_dualNumbers₂Op_apply :
    (Hom.dualNumbers₂Op hh U).snd.fst a = (h.appLE U U e a).snd.fst := by
  simp [Hom.dualNumbers₂Op]
  rfl

theorem Hom.snd_snd_dualNumbers₂Op_apply :
    (Hom.dualNumbers₂Op hh U).snd.snd a = (h.appLE U U e a).snd.snd := by
  simp [Hom.dualNumbers₂Op]
  rfl

omit hh in
/-- If `Λ` is an endomorphism of `X[ε][δ]` fixing `ε` and `δ`, the operator of `Λ ≫ h₂` is the
product of the operators of `Λ ≫ p ≫ p` and of `h₂`. -/
theorem Hom.dualNumbers₂Op_comp (Λ : X.dualNumbers.dualNumbers ⟶ X.dualNumbers.dualNumbers)
    (hδ : Λ.appTop (inr 1 : DualNumber (DualNumber Γ(X, ⊤))) = inr 1)
    (hε : Λ.appTop (inl (inr 1) : DualNumber (DualNumber Γ(X, ⊤))) = inl (inr 1))
    {h₁ h₂ : X.dualNumbers.dualNumbers ⟶ X}
    (hΛ : Λ ≫ X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj = h₁)
    (hh₁ : X.dualNumbersι ≫ X.dualNumbers.dualNumbersι ≫ h₁ = 𝟙 X)
    (hh₂ : X.dualNumbersι ≫ X.dualNumbers.dualNumbersι ≫ h₂ = 𝟙 X)
    (hh₃ : X.dualNumbersι ≫ X.dualNumbers.dualNumbersι ≫ Λ ≫ h₂ = 𝟙 X) :
    Hom.dualNumbers₂Op hh₃ U = Hom.dualNumbers₂Op hh₁ U * Hom.dualNumbers₂Op hh₂ U := by
  have e₁ := le_preimage_self_of_dualNumbersι₂_comp_eq_id hh₁ U
  have e₂ := le_preimage_self_of_dualNumbersι₂_comp_eq_id hh₂ U
  have e₃ := le_preimage_self_of_dualNumbersι₂_comp_eq_id hh₃ U
  have eΛ : U ≤ Λ ⁻¹ᵁ U := by
    intro x hx
    have := e₁ hx
    rw [← hΛ] at this
    exact this
  have e' : U ≤ (Λ ≫ X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj) ⁻¹ᵁ U := hΛ ▸ e₁
  have hA (b : Γ(X, U)) :
      (Λ ≫ X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj).appLE U U e' b = h₁.appLE U U e₁ b :=
    Hom.appLE_apply_eq_of_eq hΛ U U e' e₁ b
  have H (b : Γ(X, U)) := appLE_dualNumbers_dualNumbers_self Λ hδ hε U eΛ e' (h₂.appLE U U e₂ b)
  have hc (b : Γ(X, U)) : (Λ ≫ h₂).appLE U U e₃ b = Λ.appLE U U eΛ (h₂.appLE U U e₂ b) :=
    Hom.appLE_comp_apply Λ h₂ U U U e₂ eΛ e₃ b
  simp only [hA] at H
  refine TrivSqZeroExt.ext (TrivSqZeroExt.ext ?_ ?_) (TrivSqZeroExt.ext ?_ ?_)
  · simp
  · ext b
    simp only [fst_mul, snd_mul, Hom.fst_fst_dualNumbers₂Op, smul_eq_mul, op_smul_eq_mul,
      mul_one, one_mul, addMonoidEnd_add_apply]
    rw [Hom.fst_snd_dualNumbers₂Op_apply hh₃ U e₃, Hom.fst_snd_dualNumbers₂Op_apply hh₁ U e₁,
      Hom.fst_snd_dualNumbers₂Op_apply hh₂ U e₂, hc, (H b).2.1,
      fst_fst_appLE_of_dualNumbersι₂_comp_eq_id hh₂ U e₂,
      fst_fst_appLE_of_dualNumbersι₂_comp_eq_id hh₁ U e₁, add_comm]
  · ext b
    simp only [fst_mul, snd_mul, fst_add, Hom.fst_fst_dualNumbers₂Op, smul_eq_mul,
      op_smul_eq_mul, mul_one, one_mul, addMonoidEnd_add_apply]
    rw [Hom.snd_fst_dualNumbers₂Op_apply hh₃ U e₃, Hom.snd_fst_dualNumbers₂Op_apply hh₁ U e₁,
      Hom.snd_fst_dualNumbers₂Op_apply hh₂ U e₂, hc, (H b).2.2.1,
      fst_fst_appLE_of_dualNumbersι₂_comp_eq_id hh₂ U e₂,
      fst_fst_appLE_of_dualNumbersι₂_comp_eq_id hh₁ U e₁, add_comm]
  · ext b
    simp only [snd_mul, snd_add, Hom.fst_fst_dualNumbers₂Op, smul_eq_mul,
      op_smul_eq_mul, mul_one, one_mul, addMonoidEnd_add_apply, AddMonoid.End.coe_mul,
      Function.comp_apply]
    rw [Hom.snd_snd_dualNumbers₂Op_apply hh₃ U e₃, Hom.snd_snd_dualNumbers₂Op_apply hh₁ U e₁,
      Hom.snd_snd_dualNumbers₂Op_apply hh₂ U e₂, Hom.snd_fst_dualNumbers₂Op_apply hh₁ U e₁,
      Hom.fst_snd_dualNumbers₂Op_apply hh₁ U e₁, Hom.snd_fst_dualNumbers₂Op_apply hh₂ U e₂,
      Hom.fst_snd_dualNumbers₂Op_apply hh₂ U e₂, hc, (H b).2.2.2,
      fst_fst_appLE_of_dualNumbersι₂_comp_eq_id hh₂ U e₂,
      fst_fst_appLE_of_dualNumbersι₂_comp_eq_id hh₁ U e₁]
    abel

end Two

end Scheme

end AlgebraicGeometry
