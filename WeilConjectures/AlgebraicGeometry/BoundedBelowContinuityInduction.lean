/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-! # Finite descending induction for bounded-below continuity

Source: Stacks Tag 0GIU, the descent on the lower cohomological bound.
(blueprint: lem-sf-bounded-below-continuity-induction).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace DerivedCategory.Plus

/-- A degreewise property of bounded-below complexes holds everywhere if it holds
below the lower bound, on complexes concentrated in one degree, and is preserved
by the truncation step of Stacks Tag 0GIU.

Proof: for a complex with lower bound `a`, induct on a natural number `n` with
`p < a + n`. The case `n = 0` is vanishing. Split at `a+1`. The lower truncation
is concentrated in degree `a`; the upper truncation has lower bound `a+1`, so the
induction hypothesis applies in every degree at most `p`. Every fixed `p` admits
a finite `n`, and every object of `D⁺` admits a lower bound.
(blueprint: lem-sf-bounded-below-continuity-induction). -/
theorem property_of_vanishing_pure_truncation
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : Plus C → ℤ → Prop)
    (hzero : ∀ (K : Plus C) (a p : ℤ), K.IsGE a → p < a → P K p)
    (hpure : ∀ (K : Plus C) (a p : ℤ), K.IsGE a → K.IsLE a → P K p)
    (hstep : ∀ (K : Plus C) (a p : ℤ), K.IsGE a →
      (∀ q : ℤ, P ((TStructure.t.truncLT (a + 1)).obj K) q) →
      (∀ q : ℤ, q ≤ p → P ((TStructure.t.truncGE (a + 1)).obj K) q) → P K p)
    (K : Plus C) (p : ℤ) : P K p := by
  have H (n : ℕ) : ∀ (a : ℤ) (L : Plus C), L.IsGE a →
      ∀ q : ℤ, q < a + n → P L q := by
    induction n with
    | zero =>
      intro a L hL q hq
      exact hzero L a q hL (by simpa using hq)
    | succ n ih =>
      intro a L hL q hq
      let : L.IsGE a := hL
      apply hstep L a q hL
      · intro r
        have hGE : ((TStructure.t.truncLT (a + 1)).obj L).IsGE a := inferInstance
        have hLE : ((TStructure.t.truncLT (a + 1)).obj L).IsLE a :=
          TStructure.t.isLE_truncLT_obj L (a + 1) a (by omega)
        exact hpure _ a r hGE hLE
      · intro r hr
        exact ih (a + 1) _ (by infer_instance) r (by omega)
  obtain ⟨a, ha⟩ := K.property
  have hK : K.IsGE a := (isGE_ι_obj_iff K a).1 ha
  exact H (p - a + 1).toNat a K hK p (by omega)

end DerivedCategory.Plus
