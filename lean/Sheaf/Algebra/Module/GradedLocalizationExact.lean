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

/-- Localization at a homogeneous element preserves exactness, both on the whole module
and on its degree-zero part (Stacks, Tag 09MR, Mayer–Vietoris paragraph).
The arbitrary index set `I` indexes adjacent triples: one triple is obtained with `I = Unit`,
and the triples at all positions of any finite or infinite exact sequence give its termwise
version. The last equivalence expresses image equals kernel for the restricted maps, using
underlying sets rather than introducing another localization type.

Step 1: forget gradings and apply localization exactness
(lem-weil-pbc-localization-module-exact, Mathlib's `LocalizedModule.map_exact`) at powers of `s`.
Step 2: the induced maps preserve degrees, since they send `m/s^k` to `f(m)/s^k` or `g(m)/s^k`.
For a degree-zero element in the kernel, Step 1 supplies a preimage. Decompose that preimage
into its finitely many homogeneous components and take its degree-zero component; preservation
of degrees makes its image the original element. The converse follows from `g ∘ f = 0`.
Apply these two steps independently at every index to obtain the finite/infinite consequence.
(blueprint: lem-sc-graded-localization-exact) -/
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
  sorry

end LocalizedModule
