/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Kernel base change for a two-term complex

Source: Stacks Project, Algebra, proof of Tag 00S2, final paragraph
(blueprint: lem-weil-pbc-two-term-complex-kernel-base-change).

The algebra clause uses tensor symmetry to place the algebra factor first, where Mathlib's
`LinearMap.tensorKer` is already linear over that algebra.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace LinearMap

/-- The inclusion of the kernel tensored with `C` identifies it with the kernel after tensoring.
Source: Stacks Project, Algebra, proof of Tag 00S2, final paragraph
(blueprint: lem-weil-pbc-two-term-complex-kernel-base-change).

Proof: (1) Factor `δ` through its image `I`, giving the short exact sequences
`0 → ker δ → N₁ → I → 0` and `0 → I → N₀ → coker δ → 0`.
(2) By `lem-weil-pbc-tor-long-exact-first-variable` and the first Tor vanishing,
`I ⊗ C → N₀ ⊗ C` is injective.
(3) By `lem-weil-pbc-tor-dimension-shift-free`, freeness of `N₀` identifies
`Tor₁(I,C)` with `Tor₂(coker δ,C)`, which vanishes.
(4) Apply the first-variable Tor exact sequence to the first short exact sequence:
`ker δ ⊗ C → N₁ ⊗ C` is injective with image the kernel of `N₁ ⊗ C → I ⊗ C`.
(5) The injectivity in step 2 identifies this last kernel with `ker (δ ⊗ id)`.
Thus the displayed inclusion induces the required linear equivalence. -/
theorem exists_twoTermKernelBaseChange_equiv
    (B C N₁ N₀ : Type u) [CommRing B]
    [AddCommGroup C] [Module B C]
    [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₀] [Module B N₀]
    [Module.Free B N₀] (δ : N₁ →ₗ[B] N₀)
    (hTor₁ : IsZero (((Tor' (ModuleCat B) 1).obj
      (ModuleCat.of B (N₀ ⧸ LinearMap.range δ))).obj (ModuleCat.of B C)))
    (hTor₂ : IsZero (((Tor' (ModuleCat B) 2).obj
      (ModuleCat.of B (N₀ ⧸ LinearMap.range δ))).obj (ModuleCat.of B C))) :
    ∃ e : (LinearMap.ker δ ⊗[B] C) ≃ₗ[B] LinearMap.ker (δ.rTensor C),
      ∀ x : LinearMap.ker δ ⊗[B] C,
        (e x : N₁ ⊗[B] C) = (LinearMap.ker δ).subtype.rTensor C x := by
  sorry

/-- When `C` is a `B`-algebra, the same canonical kernel map is a `C`-linear isomorphism.
Tensor symmetry identifies this map with the one in `exists_twoTermKernelBaseChange_equiv`.
Source: Stacks Project, Algebra, proof of Tag 00S2, final paragraph
(blueprint: lem-weil-pbc-two-term-complex-kernel-base-change).

Proof: Steps 1--5 of the node proof give bijectivity as in the preceding statement.
On generators the map sends `c ⊗ h` to `c ⊗ h.val`, so it commutes with multiplication
on the `C` factor. Mathlib's `tensorKer C C δ` records this `C`-linearity already;
bijectivity therefore makes it a `C`-linear isomorphism. -/
theorem bijective_twoTermKernelBaseChange_algebra
    (B C N₁ N₀ : Type u) [CommRing B] [CommRing C] [Algebra B C]
    [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₀] [Module B N₀]
    [Module.Free B N₀] (δ : N₁ →ₗ[B] N₀)
    (hTor₁ : IsZero (((Tor' (ModuleCat B) 1).obj
      (ModuleCat.of B (N₀ ⧸ LinearMap.range δ))).obj (ModuleCat.of B C)))
    (hTor₂ : IsZero (((Tor' (ModuleCat B) 2).obj
      (ModuleCat.of B (N₀ ⧸ LinearMap.range δ))).obj (ModuleCat.of B C))) :
    Function.Bijective (δ.tensorKer C C) := by
  sorry

end LinearMap
