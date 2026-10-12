/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.CategoryTheory.TruncationCouple
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! Canonical truncation-couple proof step. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Exactness of the raw truncation maps for arbitrary derived-category instances.
Source: Stacks Tags 08J5, 05SE, 0148, 011Q; blueprint step 1 of thm-sp-truncation-e2
(blueprint: lem-sp-truncation-raw-exact).

Proof: The triangle tau<=q-1 K -> tau<=q K -> H^q(K)[-q] with the boundary
chosen by `TruncationCouple.existsUnique_boundary` is distinguished. Apply the
triangulated right derived functor and its homology sequence. Transport exactness
across the three bridge isomorphisms. The g-f and f-alpha pairs use the triangle at q,
in total degrees p+q
and p+q+1 respectively; the alpha-g pair uses the triangle at q+1, in total
degree p+q.
The index identities preserve total degree, and transport of exact short complexes
preserves both their zero composites and their image-equals-kernel condition. -/
theorem truncation_raw_exact
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) :
    let g : ∀ p q : ℤ, TruncationCouple.D F K p q ⟶
        TruncationCouple.E F K (p + (0 : ℕ)) (q - (0 : ℕ)) :=
      fun p q ↦ TruncationCouple.g F K p q ≫ eqToHom (by simp)
    (∀ p q : ℤ,
      ∃ w : TruncationCouple.f F K p q ≫
          TruncationCouple.alpha F K (p + 2) (q - 1) = 0,
        (ShortComplex.mk _ _ w).Exact) ∧
    (∀ p q : ℤ,
      ∃ w : g p q ≫ TruncationCouple.f F K (p + (0 : ℕ)) (q - (0 : ℕ)) = 0,
        (ShortComplex.mk _ _ w).Exact) ∧
    (∀ p q : ℤ,
      ∃ w : TruncationCouple.alpha F K p q ≫ g (p - 1) (q + 1) = 0,
        (ShortComplex.mk _ _ w).Exact) := by
  sorry

end CategoryTheory
