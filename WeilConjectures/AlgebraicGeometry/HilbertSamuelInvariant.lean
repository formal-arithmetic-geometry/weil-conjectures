/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaSeries
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! # Hilbert--Samuel levels and marked-ideal orders

Source: Bierstone--Milman--Temkin, arXiv:0905.3580, sections 5.1 and 6.1
(blueprint: def-trf-hilbert-samuel-invariant).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- Inclusive summation of a numerical sequence. Source: BMT 6.1
(blueprint: def-trf-hilbert-samuel-invariant). -/
def summation (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), f i

/-- The raw local Hilbert--Samuel sequence. Source: BMT 6.1. Finite type hypotheses in
applications ensure that `toNat` is applied to finite lengths
(blueprint: def-trf-hilbert-samuel-invariant). -/
noncomputable def localFunction (X : Scheme.{u}) (x : X) (n : ℕ) : ℕ :=
  (Module.length (X.presheaf.stalk x)
    ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (n + 1))).toNat

/-- The level at any, not necessarily closed, point; the exponent is transcendence degree
of its residue field over the specified ground field. Source: BMT 6.1
(blueprint: def-trf-hilbert-samuel-invariant). -/
noncomputable def function {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (x : X) : ℕ → ℕ :=
  letI := (p.residueFieldAlgebraMap x).toAlgebra
  (summation^[Cardinal.toNat (Algebra.trdeg k (X.residueField x))]) (localFunction X x)

/-- Lexicographic strict comparison, including the first differing index. Source: BMT 6.1
(blueprint: def-trf-hilbert-samuel-invariant). -/
def lt (f g : ℕ → ℕ) : Prop := ∃ n : ℕ, (∀ i : ℕ, i < n → f i = g i) ∧ f n < g n

/-- Lexicographic non-strict comparison. Source: BMT 6.1
(blueprint: def-trf-hilbert-samuel-invariant). -/
def le (f g : ℕ → ℕ) : Prop := f = g ∨ lt f g

end AlgebraicGeometry.HilbertSamuel
