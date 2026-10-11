/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricPoints

/-!
# Geometric fibres of finite morphisms are uniformly bounded

A finite morphism `p : Y ⟶ X` to a quasi-compact scheme has a uniform bound on the number of
lifts of morphisms `Spec Ω ⟶ X` from spectra of fields: over an affine open `V = Spec A` of `X`
with preimage `Spec B`, the lifts are `A`-algebra maps `B → Ω`, which are `Ω`-linearly
independent (Dedekind), so there are at most as many as generators of the `A`-module `B`.

## Main statements

- `card_ringHom_comp_eq_le`: the algebraic bound.
- `AlgebraicGeometry.Scheme.Hom.exists_card_lifts_le_of_isFinite`: the bound for finite morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- **Embeddings of a finite algebra into a field.** If the `A`-module `B` is spanned by `s`,
then for every `γ : A →+* Ω` into a field there are at most `#s` ring maps `B →+* Ω` extending
`γ`: they are linearly independent characters, determined by their values on `s`. -/
theorem card_ringHom_comp_eq_le {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Field Ω] (s : Finset B) (hs : Submodule.span A (s : Set B) = ⊤) (γ : A →+* Ω) :
    ENat.card {ρ : B →+* Ω // ρ.comp (algebraMap A B) = γ} ≤ s.card := by
  set T := {ρ : B →+* Ω // ρ.comp (algebraMap A B) = γ}
  let f : T → (B →* Ω) := fun ρ ↦ ρ.1.toMonoidHom
  have hf : Function.Injective f := fun ρ₁ ρ₂ h ↦
    Subtype.ext (RingHom.ext fun b ↦ congrArg (fun g : B →* Ω ↦ g b) h)
  let v : T → (B → Ω) := fun ρ ↦ ⇑(f ρ)
  have hli : LinearIndependent Ω v := (linearIndependent_monoidHom B Ω).comp f hf
  let E : (B → Ω) →ₗ[Ω] (s → Ω) := LinearMap.funLeft Ω Ω Subtype.val
  let M : Submodule Ω (B → Ω) :=
    { carrier := {F | (∀ x y, F (x + y) = F x + F y) ∧ ∀ (a : A) (x : B), F (a • x) = γ a * F x}
      add_mem' := fun {F G} hF hG ↦ ⟨fun x y ↦ by simp [hF.1, hG.1]; ring,
        fun a x ↦ by simp [hF.2, hG.2]; ring⟩
      zero_mem' := ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩
      smul_mem' := fun c F hF ↦ ⟨fun x y ↦ by simp [hF.1]; ring,
        fun a x ↦ by simp [hF.2]; ring⟩ }
  have hM : Submodule.span Ω (Set.range v) ≤ M := by
    rw [Submodule.span_le]
    rintro _ ⟨ρ, rfl⟩
    refine ⟨fun x y ↦ map_add ρ.1 x y, fun a x ↦ ?_⟩
    change ρ.1 (a • x) = γ a * ρ.1 x
    simp only [Algebra.smul_def, map_mul]
    congr 1
    exact congr($(ρ.2) a)
  have hdisj : Disjoint (Submodule.span Ω (Set.range v)) (LinearMap.ker E) := by
    rw [Submodule.disjoint_def]
    intro F hF hFE
    obtain ⟨hadd, hsmul⟩ := hM hF
    have h0 (b : B) (hb : b ∈ s) : F b = 0 := congr_fun hFE ⟨b, hb⟩
    funext x
    have hx : x ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem b hb => exact h0 b hb
    | zero => simpa using hadd 0 0
    | add x y _ _ hx hy => rw [hadd, hx, hy]; simp
    | smul a x _ hx => rw [hsmul, hx]; simp
  have hli' := hli.map hdisj
  have := hli'.cardinalMk_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  simpa [ENat.card] using Cardinal.toENat.monotone' this

namespace AlgebraicGeometry

variable {Y X Z S : Scheme.{u}}

/-- Lifts along a finite morphism of affine schemes are uniformly bounded. -/
theorem Scheme.Hom.exists_card_lifts_le_of_isAffine (f : Z ⟶ S) [IsAffine Z] [IsAffine S]
    (hf : f.appTop.hom.Finite) : ∃ n : ℕ, ∀ (Ω : Type u) [Field Ω] (g : Spec (.of Ω) ⟶ S),
      ENat.card {s // s ≫ f = g} ≤ n := by
  let := f.appTop.hom.toAlgebra
  have : Module.Finite Γ(S, ⊤) Γ(Z, ⊤) := hf
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := Γ(S, ⊤)) (M := Γ(Z, ⊤))
  refine ⟨t.card, fun Ω _ g ↦ ?_⟩
  let ρ : {s // s ≫ f = g} → {ρ : Γ(Z, ⊤) →+* Ω // ρ.comp (algebraMap Γ(S, ⊤) Γ(Z, ⊤)) =
      (g.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom).hom} := fun s ↦
    ⟨(s.1.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom).hom, by
      have key : (s.1 ≫ f).appTop = g.appTop := congrArg _ s.2
      rw [← key, Scheme.Hom.comp_appTop]
      rfl⟩
  have hρ : Function.Injective ρ := by
    intro s₁ s₂ h
    refine Subtype.ext (ext_of_isAffine ?_)
    have h' : s₁.1.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom =
        s₂.1.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom := CommRingCat.hom_ext congr($h.1)
    simpa using h'
  exact (ENat.card_le_card_of_injective hρ).trans (card_ringHom_comp_eq_le t ht _)

/-- Lifts along `p` of a morphism into an open `V` are lifts along the restriction `p ∣_ V`. -/
theorem Scheme.Hom.card_lifts_le_card_lifts_morphismRestrict (p : Y ⟶ X) (V : X.Opens)
    {Ω : Type u} [Field Ω] (g : Spec (.of Ω) ⟶ V) :
    ENat.card {s // s ≫ p = g ≫ V.ι} ≤ ENat.card {s // s ≫ p ∣_ V = g} := by
  let h := isPullback_morphismRestrict p V
  refine ENat.card_le_card_of_injective (f := fun s ↦ ⟨h.lift g s.1 s.2.symm, h.lift_fst _ _ _⟩)
    fun s₁ s₂ hs ↦ Subtype.ext ?_
  rw [← h.lift_snd g s₁.1 s₁.2.symm, ← h.lift_snd g s₂.1 s₂.2.symm]
  exact congr($hs.1 ≫ _)

/-- **Geometric fibres of finite morphisms are uniformly bounded.** For a finite morphism
`p : Y ⟶ X` to a quasi-compact scheme there is `n` such that every morphism `Spec Ω ⟶ X` from the
spectrum of a field has at most `n` lifts along `p`. -/
theorem Scheme.Hom.exists_card_lifts_le_of_isFinite (p : Y ⟶ X) [IsFinite p] [CompactSpace X] :
    ∃ n : ℕ, ∀ (Ω : Type u) [Field Ω] (g : Spec (.of Ω) ⟶ X), ENat.card {s // s ≫ p = g} ≤ n := by
  have hbound (V : X.affineOpens) : ∃ n : ℕ, ∀ (Ω : Type u) [Field Ω] (g : Spec (.of Ω) ⟶ V.1),
      ENat.card {s // s ≫ p ∣_ V.1 = g} ≤ n := by
    have : IsAffine V.1.toScheme := V.2
    have : IsAffine (p ⁻¹ᵁ V.1).toScheme := V.2.preimage p
    exact (p ∣_ V.1).exists_card_lifts_le_of_isAffine (Scheme.Hom.finite_appTop _)
  choose n hn using hbound
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V.1 : Set X))
    (fun V ↦ V.1.2) fun x _ ↦ by
      obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩
  refine ⟨s.sup n, fun Ω _ g ↦ ?_⟩
  obtain ⟨a⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  obtain ⟨V, hV, hgV⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ (g a)))
  have hr : Set.range g.base ⊆ Set.range V.1.ι.base := by
    rintro _ ⟨b, rfl⟩
    rw [Subsingleton.elim b a, Scheme.Opens.range_ι]
    exact hgV
  obtain ⟨g', rfl⟩ : ∃ g', g' ≫ V.1.ι = g := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  calc _ ≤ _ := p.card_lifts_le_card_lifts_morphismRestrict V.1 g'
    _ ≤ n V := hn V Ω g'
    _ ≤ s.sup n := by exact_mod_cast Finset.le_sup hV

end AlgebraicGeometry
