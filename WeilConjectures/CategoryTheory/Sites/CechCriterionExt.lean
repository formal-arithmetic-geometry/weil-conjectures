/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechCriterion

/-!
# The Čech criterion for `Ext` out of a corepresenting object

This is a variant of the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`
(Cartan's criterion, [Stacks 03F7]) for an abelian category `𝒜` with a left exact functor
`Φ : 𝒜 ⥤ Sheaf J AddCommGrpCat` preserving epimorphisms, for instance sheaves of modules with
the functor forgetting the module structure. Let `G` be an object of `𝒜` corepresenting the
sections of `Φ` over an object `T` of the site. If the Čech complexes of `Φ I` are exact in
positive degrees for every injective object `I`, and the Čech complexes of `Φ F` are exact in
positive degrees on the finite covering families of a class `B` of objects as in the Čech
criterion, then `Extᵠ(G, F) = 0` for `q > 0`.

## Main statements

- `CategoryTheory.Sheaf.subsingleton_ext_succ_of_exactAt_cechComplex`: the criterion.
-/

@[expose] public section

universe w' v' u' v w

open CategoryTheory Limits Opposite Abelian Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max w v}]
  {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜]
  (Φ : 𝒜 ⥤ Sheaf J AddCommGrpCat.{max w v}) [Φ.Additive] [PreservesFiniteLimits Φ]
  [Φ.PreservesEpimorphisms]

/-- A left exact functor preserving epimorphisms preserves short exact sequences. -/
lemma shortExact_map_of_preservesFiniteLimits {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    (S.map Φ).ShortExact :=
  have := hS.mono_f
  have := hS.epi_g
  .mk' (hS.exact.map_of_mono_of_preservesKernel Φ hS.mono_f inferInstance)
    (inferInstanceAs (Mono (Φ.map S.f))) (inferInstanceAs (Epi (Φ.map S.g)))

variable [HasExt.{w'} 𝒜] [EnoughInjectives 𝒜] [∀ V : C, HasFiniteProducts (Over V)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w v}]

/-- **The Čech criterion for `Ext` out of a corepresenting object.** Let `Φ : 𝒜 ⥤ Sheaf J Ab`
be left exact and preserve epimorphisms, and let `G` corepresent the sections of `Φ` over the
object `T` of the site, via `e`. Suppose that the Čech complexes of `Φ I` are exact in positive
degrees for every injective object `I` of `𝒜`. Let `B` be a class of objects of the site
containing `T`, such that every covering sieve of a member `V` of `B` contains a finite family
`U` generating a covering sieve, whose Čech nerve lies in `B`. If the Čech complexes of `Φ F`
on all these families are exact in positive degrees, then `Extᵠ(G, F) = 0` for `q > 0`. -/
@[stacks 03F7]
theorem subsingleton_ext_succ_of_exactAt_cechComplex (G : 𝒜) {T : C}
    (e : ∀ F : 𝒜, (G ⟶ F) ≃ (Φ.obj F).obj.obj (op T))
    (he : ∀ {F F' : 𝒜} (f : G ⟶ F) (g : F ⟶ F'),
      e F' (f ≫ g) = (Φ.map g).hom.app (op T) (e F f))
    (hinj : ∀ (I : 𝒜) [Injective I] {V : C} {n : ℕ} (U : Fin n → Over V) (q : ℕ),
      ((cechComplex U).obj (Φ.obj I).obj).ExactAt (q + 1))
    (B : C → Prop) (hBT : B T)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (F : 𝒜)
    (hF : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
      ∀ q : ℕ, ((cechComplex U).obj (Φ.obj F).obj).ExactAt (q + 1))
    (q : ℕ) : Subsingleton (Ext.{w'} G F (q + 1)) := by
  -- for a short exact sequence `0 → F → I → Q → 0`, sections of `Φ Q` over members of `B` lift
  have hsurj (F : 𝒜)
      (hF : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) →
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
        ∀ q : ℕ, ((cechComplex U).obj (Φ.obj F).obj).ExactAt (q + 1))
      {S : ShortComplex 𝒜} (hS : S.ShortExact) (hSF : S.X₁ = F)
      (V : C) (hV : B V) : Function.Surjective ((Φ.map S.g).hom.app (op V)) := by
    subst hSF
    refine surjective_app_of_exactAt_cechComplex_one
      (shortExact_map_of_preservesFiniteLimits Φ hS) fun R hR ↦ ?_
    obtain ⟨n, U, hUB, hUR, hUJ⟩ := hcov V hV R hR
    exact ⟨n, U, hUR, hUJ, hF V hV U hUB hUJ 0⟩
  induction q generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _) rfl
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
    obtain ⟨t, ht⟩ := hsurj F hF hS rfl T hBT (e S.X₃ g)
    obtain ⟨g', rfl⟩ := (e S.X₂).surjective t
    rw [← he] at ht
    obtain rfl := (e S.X₃).injective ht
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hS' := shortExact_map_of_preservesFiniteLimits Φ hS
    have := ih S.X₃ fun V hV n U hUB hUJ q ↦ exactAt_cechComplex_of_sectionwise U
      (Φ.map S.f).hom (Φ.map S.g).hom (app_g_app_f (S := S.map Φ)) (injective_app_f hS')
      (exists_app_f_eq hS') (fun k y ↦ hsurj F hF hS rfl _ (hUB k y)) q
      (hF V hV U hUB hUJ (q + 1)) (hinj S.X₂ U q)
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _) rfl
    rw [Subsingleton.elim y 0, Ext.zero_comp]

end CategoryTheory.Sheaf
