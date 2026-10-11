/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechCriterion

/-!
# The Čech criterion for a chosen class of covering families

This is a variant of the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` (Cartan's criterion,
[Stacks 03F7]) in which the exactness of the Čech complexes is only required on a chosen class
of finite covering families, specified by a predicate `good`: every covering sieve of a member
`V` of the class `B` of objects must contain a good family, the members of the Čech nerves of
good families must lie in `B`, and good families must generate covering sieves. This is useful
when the Čech complexes can only be controlled on families of a particular shape, such as base
changes of families from the stages of a cofiltered limit.

## Main statements

- `CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex_of_good`: the criterion.
-/

@[expose] public section

universe v w

open CategoryTheory Limits Opposite Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max w v}]
  [HasExt.{max w v} (Sheaf J AddCommGrpCat.{max w v})] {T : C}

open Abelian

variable [∀ V : C, HasFiniteProducts (Over V)]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max w v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w v}]

/-- **The Čech criterion for a chosen class of families.** Let `B` be a class of objects of the
site containing a terminal object `T`, and `good` a class of finite families of morphisms with
common target, such that every covering sieve of a member `V` of `B` contains a good family over
`V`, and good families over members of `B` generate covering sieves and have their Čech nerves in
`B`. If the Čech complexes of the abelian sheaf `F` on all good families over members of `B` are
exact in positive degrees, then `H^q(F) = 0` for `q > 0`. -/
theorem subsingleton_H_succ_of_exactAt_cechComplex_of_good (hT : IsTerminal T) (B : C → Prop)
    (hBT : B T) (good : ∀ (V : C) {n : ℕ}, (Fin n → Over V) → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V), good V U ∧ ∀ a, R (U a).hom)
    (hgood : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V), good V U →
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (F : Sheaf J AddCommGrpCat.{max w v})
    (hF : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V), good V U →
      ∀ q : ℕ, ((cechComplex U).obj F.obj).ExactAt (q + 1))
    (q : ℕ) : Subsingleton (Sheaf.H F (q + 1)) := by
  -- for a short exact sequence `0 → F → I → Q → 0`, sections of `Q` over members of `B` lift
  have hsurj (F : Sheaf J AddCommGrpCat.{max w v})
      (hF : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V), good V U →
        ∀ q : ℕ, ((cechComplex U).obj F.obj).ExactAt (q + 1))
      {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})} (hS : S.ShortExact) (hSF : S.X₁ = F)
      (V : C) (hV : B V) : Function.Surjective (S.g.hom.app (op V)) := by
    subst hSF
    refine surjective_app_of_exactAt_cechComplex_one hS fun R hR ↦ ?_
    obtain ⟨n, U, hU, hUR⟩ := hcov V hV R hR
    exact ⟨n, U, hUR, (hgood V hV U hU).2, hF V hV U hU 0⟩
  induction q generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    exact subsingleton_H_succ_of_comp_extClass hS 0
      (comp_extClass_eq_zero_of_surjective hT hS (hsurj F hF hS rfl T hBT))
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have := ih S.X₃ fun V hV n U hU q ↦ exactAt_cechComplex_of_sectionwise U S.f.hom S.g.hom
      app_g_app_f (injective_app_f hS) (exists_app_f_eq hS)
      (fun k y ↦ hsurj F hF hS rfl _ ((hgood V hV U hU).1 k y)) q (hF V hV U hU (q + 1))
      (exactAt_cechComplex_of_injective S.X₂ U q)
    exact subsingleton_H_succ_of_comp_extClass hS (q + 1) fun y ↦ by
      rw [Subsingleton.elim y 0, Ext.zero_comp]

end CategoryTheory.Sheaf
