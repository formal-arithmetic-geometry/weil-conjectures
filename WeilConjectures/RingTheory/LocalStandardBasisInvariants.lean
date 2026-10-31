/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NodalLocalTangentData
public import Mathlib.Data.ENat.Lattice

/-! # Local standard-basis invariants

Source: Hironaka, Certain numerical characters of singularities (1970), §§2–3,
pp.154–155, and Lemma 20, pp.176–181.
(blueprint: def-trf-local-standard-basis-invariants).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Hironaka

open AlgebraicGeometry.NodalLocal

/-- The ideal-adic order, including infinite order for an element in every power.
Source: Hironaka (1970), §2, pp.153–154.
(blueprint: def-trf-local-standard-basis-invariants). -/
noncomputable def adicOrder {V : Type u} [CommRing V] (J : Ideal V) (h : V) : ℕ∞ :=
  ⨆ n : {n : ℕ // h ∈ J ^ n}, (n.val : ℕ∞)

/-- An irredundant generating family of an ideal. Homogeneity and its degrees
are specified separately, so this definition does not discard repeated degrees.
Source: Hironaka (1970), Remark 1, p.155.
(blueprint: def-trf-local-standard-basis-invariants). -/
def IsMinimalGeneratingFamily {V : Type u} [CommRing V] {m : ℕ}
    (E : Ideal V) (ξ : Fin m → V) : Prop :=
  Ideal.span (Set.range ξ) = E ∧
    ∀ i, ξ i ∉ Ideal.span {z | ∃ j, j ≠ i ∧ z = ξ j}

/-- Degrees of a homogeneous family in the recorded associated graded ring.
Source: Hironaka (1970), Remark 1, p.155.
(blueprint: def-trf-local-standard-basis-invariants). -/
def HasDegrees {V : Type u} [CommRing V] (J : Ideal V) {m : ℕ}
    (d : Fin m → ℕ) (ξ : Fin m → Ideal.associatedGraded J) : Prop :=
  ∀ i, ∃ η : Ideal.associatedGradedPiece J (d i),
    ξ i = DirectSum.of (fun n ↦ Ideal.associatedGradedPiece J n) (d i) η

end Hironaka
