/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Basic

/-!
# Essentially constant inverse systems

An inverse system `(B_i)_{i ∈ ℕ}` is *essentially constant* with value `X` if there are
compatible maps `π_i : X → B_i`, an index `i₀` and a retraction `r : B_{i₀} → X` of `π_{i₀}` such
that every transition map `B_k → B_j` (for `k` large) factors as `π_j ∘ r ∘ (B_k → B_{i₀})`
(Stacks, Homology, Definition 0BKF / Tag 0BKC).

The blueprint indexes systems of abelian groups by `i ≥ 1`; we index by `ℕ` and allow any target
category.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {C : Type*} [Category C]

/-- The inverse system `B : ℕᵒᵖ ⥤ C` is *essentially constant*: there are an object `X`, maps
`π_i : X ⟶ B_i` compatible with the transition maps, an index `i₀` and `r : B_{i₀} ⟶ X` with
`π_{i₀} ≫ r = 𝟙 X`, such that for every `j` there is `k ≥ max i₀ j` with
`(B_k → B_j) = (B_k → B_{i₀}) ≫ r ≫ π_j`.
(blueprint: `def-weil-pbc-essentially-constant-system`) -/
def IsEssentiallyConstant (B : ℕᵒᵖ ⥤ C) : Prop :=
  ∃ (X : C) (π : ∀ i : ℕ, X ⟶ B.obj (op i)),
    (∀ i : ℕ, π (i + 1) ≫ B.map (homOfLE (Nat.le_succ i)).op = π i) ∧
    ∃ (i₀ : ℕ) (r : B.obj (op i₀) ⟶ X), π i₀ ≫ r = 𝟙 X ∧
      ∀ j : ℕ, ∃ (k : ℕ) (hk₀ : i₀ ≤ k) (hkj : j ≤ k),
        B.map (homOfLE hkj).op = B.map (homOfLE hk₀).op ≫ r ≫ π j

end CategoryTheory.Functor
