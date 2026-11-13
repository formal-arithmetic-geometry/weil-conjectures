/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.EtaleCoverThickeningLift
import WeilConjectures.AlgebraicGeometry.FiniteOpenPartitionThickeningTransport

/-! # Descent of finite splitting through a surjective closed immersion

## References

* Stacks Project, Tag 04DZ.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- If `a ≫ g` is a universal homeomorphism, `a` is surjective and `g` is finite, then `g` is a
universal homeomorphism (Stacks, Tag 04DF). -/
private theorem universalHomeomorphism_of_surjective_precomp
    {A B C : Scheme.{u}} (a : A ⟶ B) (g : B ⟶ C)
    [Surjective a] [IsFinite g] [IsUniversalHomeomorphism (a ≫ g)] :
    IsUniversalHomeomorphism g := by
  have : Surjective g := Surjective.of_comp a g
  have : UniversallyInjective g := by
    constructor
    intro B' C' b c g' h
    let a' := pullback.snd a b
    have : Surjective a' := inferInstance
    have hh : IsPullback (a' ≫ g') (pullback.fst a b) c (a ≫ g) :=
      (IsPullback.of_hasPullback a b).flip.paste_horiz h
    have : UniversallyInjective (a' ≫ g') :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hh.flip inferInstance
    intro y₁ y₂ hy
    obtain ⟨x₁, rfl⟩ := a'.surjective y₁
    obtain ⟨x₂, rfl⟩ := a'.surjective y₂
    exact congrArg a' ((a' ≫ g').injective hy)
  exact {}

/-- Finite étale-local splitting into universal homeomorphisms descends through a
surjective closed immersion. This is a statement over a fixed open, with no
Noetherian, density, affine, or generic-splitting assumption (Stacks, Tag 04DZ). -/
theorem finite_splitting_descends_surjective_closedImmersion
    {X Y R : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (r : R ⟶ Y) [IsClosedImmersion r] [Surjective r] (U : Y.Opens)
    (h : ∃ 𝒯 : Cover.{u} etalePrecoverage (r ⁻¹ᵁ U).toScheme, ∀ i,
      ∃ (n : ℕ)
        (W : Fin n → (pullback (𝒯.f i) (pullback.snd f r ∣_ (r ⁻¹ᵁ U))).Opens),
        (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
        ∀ j, IsUniversalHomeomorphism
          ((W j).ι ≫ pullback.fst (𝒯.f i) (pullback.snd f r ∣_ (r ⁻¹ᵁ U)))) :
    ∃ 𝒯 : Cover.{u} etalePrecoverage U.toScheme, ∀ i,
      ∃ (n : ℕ) (W : Fin n → (pullback (𝒯.f i) (f ∣_ U)).Opens),
        (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
        ∀ j, IsUniversalHomeomorphism
          ((W j).ι ≫ pullback.fst (𝒯.f i) (f ∣_ U)) := by
  obtain ⟨𝒯, h𝒯⟩ := h
  obtain ⟨𝒮, h𝒮⟩ := exists_etale_cover_thickening_lift f r U 𝒯
  refine ⟨𝒮, fun i ↦ ?_⟩
  obtain ⟨k, t, p, htClosed, htSurj, hpClosed, hpSurj, hcomm⟩ := h𝒮 i
  have : IsClosedImmersion t := htClosed
  have : Surjective t := htSurj
  have : IsClosedImmersion p := hpClosed
  have : Surjective p := hpSurj
  obtain ⟨n, W, hcover, hdisj, hW⟩ := h𝒯 k
  obtain ⟨V, hVcover, hVdisj, hV⟩ :=
    exists_finite_open_partition_thickening_transport p n W hcover hdisj
  refine ⟨n, V, hVcover, hVdisj, fun j ↦ ?_⟩
  obtain ⟨hVfinite, a, _, haSurj, ha⟩ := hV j
  have : IsFinite (V j).ι := hVfinite
  have : Surjective a := haSurj
  have : IsUniversalHomeomorphism
      ((W j).ι ≫ pullback.fst (𝒯.f k) (pullback.snd f r ∣_ (r ⁻¹ᵁ U))) := hW j
  have : IsUniversalHomeomorphism
      (a ≫ ((V j).ι ≫ pullback.fst (𝒮.f i) (f ∣_ U))) := by
    rw [← Category.assoc, ha, Category.assoc, hcomm, ← Category.assoc]
    infer_instance
  exact universalHomeomorphism_of_surjective_precomp a
    ((V j).ι ≫ pullback.fst (𝒮.f i) (f ∣_ U))

end AlgebraicGeometry.Scheme
