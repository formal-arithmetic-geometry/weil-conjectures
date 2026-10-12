/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Module

/-!
# Assembling cancellation from two split functionals

Source: Stacks Project, Algebra, Tag 00MT, proof, final three sentences.
(blueprint: lem-weil-pbc-split-identity-from-functionals).
-/

@[expose] public section

universe u v

open scoped DirectSum

namespace ChainComplex

/-- Assemble the complement and identity complex once the neighboring maps respect the split.
Source: Stacks Project, Algebra, Tag 00MT, proof, final three sentences.
(blueprint: lem-weil-pbc-split-identity-from-functionals).

Proof: Let the complementary terms be `ker α`, `ker β` at `i`, `i - 1`, and the original
terms elsewhere. The equality `β ∘ d = α` restricts the middle differential to these
kernels; `hin` restricts the incoming differential; all other differentials restrict
without a codomain change. The restricted differentials square to zero by the original
complex relation and injectivity of submodule inclusions. Let `T` have a universe lift of
`R` at `i`, `i - 1`, zero terms elsewhere and the identity as middle differential.
The degreewise decompositions are `x = (x - α(x) • z) + α(x) • z` at `i` and
`y = (y - β(y) • w) + β(y) • w` at `i - 1`; the kernel components are unique since
`α(z) = β(w) = 1`. Use these decompositions to make the degreewise binary-direct-sum
linear equivalences. In degree `i + 1` compatibility is `hin`; in degree `i` it follows
from `hd` and `hdz`; in degree `i - 1` it is `hout`; in all other degrees it is the
identity. No finiteness or freeness is required, and the construction includes the zero
ring. The displayed equivalences `g` identify the complement with these exact submodules. -/
theorem exists_splitting_of_split_functionals
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℤ)
    (i : ℤ) (α : C.X i →ₗ[R] R) (β : C.X (i - 1) →ₗ[R] R)
    (z : C.X i) (w : C.X (i - 1))
    (hz : α z = 1) (hw : β w = 1)
    (hd : ∀ x, β ((C.d i (i - 1)).hom x) = α x)
    (hdz : (C.d i (i - 1)).hom z = w)
    (hin : ∀ x, α ((C.d (i + 1) i).hom x) = 0)
    (hout : (C.d (i - 1) (i - 2)).hom w = 0) :
    let S : ∀ j : ℤ, Submodule R (C.X j) := fun j ↦
      if h : j = i then h ▸ LinearMap.ker α
      else if h : j = i - 1 then h ▸ LinearMap.ker β else ⊤
    ∃ (C' T : ChainComplex (ModuleCat.{max u v} R) ℤ)
      (g : ∀ j, C'.X j ≃ₗ[R] S j),
      (∀ j : ℤ, j ≠ i → j ≠ i - 1 → Subsingleton (T.X j)) ∧
      ∃ (e : T.X i ≃ₗ[R] R) (f : T.X (i - 1) ≃ₗ[R] R),
        (∀ t : T.X i, f ((T.d i (i - 1)).hom t) = e t) ∧
        let M : ℤ → Bool → ModuleCat.{max u v} R :=
          fun j s ↦ if s then T.X j else C'.X j
        ∃ ψ : ∀ j : ℤ, (⨁ s : Bool, M j s) ≃ₗ[R] C.X j,
          ∀ (j : ℤ) (x : C'.X j) (t : T.X j),
            (C.d j (j - 1)).hom
                (ψ j (DirectSum.lof R Bool (fun s ↦ M j s) false x +
                  DirectSum.lof R Bool (fun s ↦ M j s) true t)) =
              ψ (j - 1)
                (DirectSum.lof R Bool (fun s ↦ M (j - 1) s) false
                    ((C'.d j (j - 1)).hom x) +
                  DirectSum.lof R Bool (fun s ↦ M (j - 1) s) true
                    ((T.d j (j - 1)).hom t)) := by
  sorry

end ChainComplex
