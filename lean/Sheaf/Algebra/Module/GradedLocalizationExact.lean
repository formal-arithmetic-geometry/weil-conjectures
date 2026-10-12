/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Sheaf.Algebra.Module.LocalizedHomogeneousPiece

/-!
# Exactness of homogeneous module localization and degree-zero parts

Source: Stacks Project, Cohomology of Schemes, Tag 09MR, Mayer–Vietoris paragraph
(blueprint: lem-sc-graded-localization-exact).
-/

@[expose] public section

universe u v₀ v₁ v₂ w

namespace LocalizedModule

/-- Intermediate degree-zero exactness, split from the target proof.

Proof plan (Stacks Project, Cohomology of Schemes, Tag 09MR, Mayer--Vietoris
paragraph): first apply ordinary localization exactness to obtain a preimage of a
degree-zero element in the kernel.  Represent that preimage by a finite sum of
fractions and use `DirectSum.decompose` for the internal decomposition of the
source.  The degree-preservation hypothesis implies that the localized map sends
the degree-zero component to the degree-zero component of the image; all other
components map to distinct degrees and therefore have zero degree-zero component.
Consequently the degree-zero component is still a preimage of the original
element and lies in `homogeneousPieceAway`.  The reverse implication follows
from `Function.Exact`, since the composite localized map is zero.  The
construction is valid also for `d = 0` and for the zero localized module.
(blueprint: lem-sc-graded-localization-degree-zero-exact) -/
theorem graded_localization_degree_zero_exact {A : Type u} [CommRing A]
    (𝓐 : ℤ → AddSubgroup A) (_h𝓐 : DirectSum.IsInternal 𝓐)
    (_hmul : ∀ (a b : ℤ) (r t : A), r ∈ 𝓐 a → t ∈ 𝓐 b → r * t ∈ 𝓐 (a + b))
    (s : A) (d : ℤ) (_hd : 0 ≤ d) (_hs : s ∈ 𝓐 d)
    {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module A M₀] [Module A M₁] [Module A M₂]
    (𝓜₀ : ℤ → AddSubgroup M₀) (𝓜₁ : ℤ → AddSubgroup M₁)
    (𝓜₂ : ℤ → AddSubgroup M₂)
    (_h𝓜₀ : DirectSum.IsInternal 𝓜₀) (_h𝓜₁ : DirectSum.IsInternal 𝓜₁)
    (_h𝓜₂ : DirectSum.IsInternal 𝓜₂)
    (_hsmul₀ : ∀ (a b : ℤ) (r : A) (m : M₀), r ∈ 𝓐 a → m ∈ 𝓜₀ b → r • m ∈ 𝓜₀ (a + b))
    (_hsmul₁ : ∀ (a b : ℤ) (r : A) (m : M₁), r ∈ 𝓐 a → m ∈ 𝓜₁ b → r • m ∈ 𝓜₁ (a + b))
    (_hsmul₂ : ∀ (a b : ℤ) (r : A) (m : M₂), r ∈ 𝓐 a → m ∈ 𝓜₂ b → r • m ∈ 𝓜₂ (a + b))
    (f : M₀ →ₗ[A] M₁) (g : M₁ →ₗ[A] M₂)
    (hf : ∀ n x, x ∈ 𝓜₀ n → f x ∈ 𝓜₁ n)
    (hg : ∀ n x, x ∈ 𝓜₁ n → g x ∈ 𝓜₂ n)
    (hex : Function.Exact f g) :
    ∀ y ∈ homogeneousPieceAway 𝓜₁ s d 0,
      (IsLocalizedModule.map (Submonoid.powers s) (mkLinearMap (Submonoid.powers s) M₁)
        (mkLinearMap (Submonoid.powers s) M₂) g) y = 0 ↔
      ∃ x ∈ homogeneousPieceAway 𝓜₀ s d 0,
        (IsLocalizedModule.map (Submonoid.powers s) (mkLinearMap (Submonoid.powers s) M₀)
          (mkLinearMap (Submonoid.powers s) M₁) f) x = y := by
  sorry

theorem graded_localization_exact {A : Type u} [CommRing A]
    (𝓐 : ℤ → AddSubgroup A) (_h𝓐 : DirectSum.IsInternal 𝓐)
    (_hmul : ∀ (a b : ℤ) (r t : A), r ∈ 𝓐 a → t ∈ 𝓐 b → r * t ∈ 𝓐 (a + b))
    (s : A) (d : ℤ) (_hd : 0 ≤ d) (_hs : s ∈ 𝓐 d) (I : Type w)
    (M₀ : I → Type v₀) (M₁ : I → Type v₁) (M₂ : I → Type v₂)
    [∀ i, AddCommGroup (M₀ i)] [∀ i, AddCommGroup (M₁ i)] [∀ i, AddCommGroup (M₂ i)]
    [∀ i, Module A (M₀ i)] [∀ i, Module A (M₁ i)] [∀ i, Module A (M₂ i)]
    (𝓜₀ : ∀ i, ℤ → AddSubgroup (M₀ i)) (𝓜₁ : ∀ i, ℤ → AddSubgroup (M₁ i))
    (𝓜₂ : ∀ i, ℤ → AddSubgroup (M₂ i))
    (_h𝓜₀ : ∀ i, DirectSum.IsInternal (𝓜₀ i)) (_h𝓜₁ : ∀ i, DirectSum.IsInternal (𝓜₁ i))
    (_h𝓜₂ : ∀ i, DirectSum.IsInternal (𝓜₂ i))
    (_hsmul₀ : ∀ i (a b : ℤ) (r : A) (m : M₀ i), r ∈ 𝓐 a → m ∈ 𝓜₀ i b → r • m ∈ 𝓜₀ i (a + b))
    (_hsmul₁ : ∀ i (a b : ℤ) (r : A) (m : M₁ i), r ∈ 𝓐 a → m ∈ 𝓜₁ i b → r • m ∈ 𝓜₁ i (a + b))
    (_hsmul₂ : ∀ i (a b : ℤ) (r : A) (m : M₂ i), r ∈ 𝓐 a → m ∈ 𝓜₂ i b → r • m ∈ 𝓜₂ i (a + b))
    (f : ∀ i, M₀ i →ₗ[A] M₁ i) (g : ∀ i, M₁ i →ₗ[A] M₂ i)
    (hf : ∀ i n x, x ∈ 𝓜₀ i n → f i x ∈ 𝓜₁ i n)
    (hg : ∀ i n x, x ∈ 𝓜₁ i n → g i x ∈ 𝓜₂ i n)
    (hex : ∀ i, Function.Exact (f i) (g i)) :
    ∀ i,
      let fₛ := IsLocalizedModule.map (Submonoid.powers s)
        (mkLinearMap (Submonoid.powers s) (M₀ i))
        (mkLinearMap (Submonoid.powers s) (M₁ i)) (f i)
      let gₛ := IsLocalizedModule.map (Submonoid.powers s)
        (mkLinearMap (Submonoid.powers s) (M₁ i))
        (mkLinearMap (Submonoid.powers s) (M₂ i)) (g i)
      Function.Exact fₛ gₛ ∧
      (∀ n, Set.MapsTo fₛ (homogeneousPieceAway (𝓜₀ i) s d n)
        (homogeneousPieceAway (𝓜₁ i) s d n)) ∧
      (∀ n, Set.MapsTo gₛ (homogeneousPieceAway (𝓜₁ i) s d n)
        (homogeneousPieceAway (𝓜₂ i) s d n)) ∧
      (∀ y ∈ homogeneousPieceAway (𝓜₁ i) s d 0,
        gₛ y = 0 ↔ ∃ x ∈ homogeneousPieceAway (𝓜₀ i) s d 0, fₛ x = y) := by
  intro i
  let T := Submonoid.powers s
  let fₛ := IsLocalizedModule.map T (mkLinearMap T (M₀ i))
    (mkLinearMap T (M₁ i)) (f i)
  let gₛ := IsLocalizedModule.map T (mkLinearMap T (M₁ i))
    (mkLinearMap T (M₂ i)) (g i)
  have hExact : Function.Exact fₛ gₛ :=
    IsLocalizedModule.map_exact T _ _ _ (f i) (g i) (hex i)
  refine ⟨hExact, ?_, ?_, ?_⟩
  · intro n x hx
    rcases hx with ⟨k, m, hm, rfl⟩
    refine ⟨k, f i m, hf i _ _ hm, ?_⟩
    exact (IsLocalizedModule.map_LocalizedModules T (f i) m _).symm
  · intro n x hx
    rcases hx with ⟨k, m, hm, rfl⟩
    refine ⟨k, g i m, hg i _ _ hm, ?_⟩
    exact (IsLocalizedModule.map_LocalizedModules T (g i) m _).symm
  · exact graded_localization_degree_zero_exact 𝓐 _h𝓐 _hmul s d _hd _hs
      (𝓜₀ i) (𝓜₁ i) (𝓜₂ i) (_h𝓜₀ i) (_h𝓜₁ i) (_h𝓜₂ i)
      (_hsmul₀ i) (_hsmul₁ i) (_hsmul₂ i) (f i) (g i) (hf i) (hg i) (hex i)

end LocalizedModule
