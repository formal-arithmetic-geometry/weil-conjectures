/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechCriterion

/-!
# The Čech criterion with a class of good covering families

A variant of `CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` in which the
exactness of the Čech complexes is only required on a class `𝒞` of *good* finite families,
provided every covering sieve of a member of `B` contains a good family generating a covering
sieve. The proof is the same dimension shifting argument: the Čech complexes of the cokernel of
an injective embedding are exact on the same good families.
-/

@[expose] public section

universe w' v w

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

open Presheaf Abelian

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max w v}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{max w v})] {T : C} (hT : IsTerminal T)
  [∀ V : C, HasFiniteProducts (Over V)]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max w v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w v}]

include hT in
/-- **The Čech criterion with good families.** Let `B` be a class of objects of the site
containing a terminal object `T` and `𝒞` a class of finite families of objects over members of
`B`, such that every covering sieve of a member `V` of `B` contains a family in `𝒞` generating a
covering sieve, whose Čech nerve lies in `B`. If the Čech complexes of the abelian sheaf `F` on
all these good families are exact in positive degrees, then `H^q(F) = 0` for `q > 0`. -/
theorem subsingleton_H_succ_of_exactAt_cechComplex_of_good (B : C → Prop) (hBT : B T)
    (𝒞 : ∀ (V : C) {n : ℕ}, (Fin n → Over V) → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V), 𝒞 V U ∧
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (F : Sheaf J AddCommGrpCat.{max w v})
    (hF : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V), 𝒞 V U →
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
      ∀ q : ℕ, ((cechComplex U).obj F.obj).ExactAt (q + 1))
    (q : ℕ) : Subsingleton (Sheaf.H F (q + 1)) := by
  -- for a short exact sequence `0 → F → I → Q → 0`, sections of `Q` over members of `B` lift
  have hsurj (F : Sheaf J AddCommGrpCat.{max w v})
      (hF : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V), 𝒞 V U →
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) →
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
        ∀ q : ℕ, ((cechComplex U).obj F.obj).ExactAt (q + 1))
      {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})} (hS : S.ShortExact) (hSF : S.X₁ = F)
      (V : C) (hV : B V) : Function.Surjective (S.g.hom.app (op V)) := by
    subst hSF
    refine surjective_app_of_exactAt_cechComplex_one hS fun R hR ↦ ?_
    obtain ⟨n, U, hU𝒞, hUB, hUR, hUJ⟩ := hcov V hV R hR
    exact ⟨n, U, hUR, hUJ, hF V hV U hU𝒞 hUB hUJ 0⟩
  induction q generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    exact subsingleton_H_succ_of_comp_extClass hS 0
      (comp_extClass_eq_zero_of_surjective hT hS (hsurj F hF hS rfl T hBT))
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have := ih S.X₃ fun V hV n U hU𝒞 hUB hUJ q ↦ exactAt_cechComplex_of_sectionwise U S.f.hom
      S.g.hom app_g_app_f (injective_app_f hS) (exists_app_f_eq hS)
      (fun k y ↦ hsurj F hF hS rfl _ (hUB k y)) q (hF V hV U hU𝒞 hUB hUJ (q + 1))
      (exactAt_cechComplex_of_injective S.X₂ U q)
    exact subsingleton_H_succ_of_comp_extClass hS (q + 1) fun y ↦ by
      rw [Subsingleton.elim y 0, Ext.zero_comp]

end CategoryTheory.Sheaf
