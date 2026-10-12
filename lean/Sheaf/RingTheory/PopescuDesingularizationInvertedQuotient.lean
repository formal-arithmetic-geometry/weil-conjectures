/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal

/-! # The desingularization quotient after inverting the parameter

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR, the identification
`B_π = A_π[v]`.
-/

@[expose] public section

universe u w

namespace Algebra

open MvPolynomial

/-- Inverting the parameter in the substituted quotient eliminates the `w` variables.
This is a purely algebraic assertion, independent of smoothness and the map to `Λ`.

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR, paragraph beginning
with the identification of `B_π` with `A_π[v]`.
(blueprint: lem-weil-pbc-popescu-desingularization-inverted-quotient).

Proof: write `Q = R[v,w]`, `Fⱼ = fⱼ(ξ)` and `ξᵢ = π²Σₖsᵢₖvₖ + π³wᵢ`.
The iterated quotient in the statement is `Q/(g,F)`. After inverting `π`, each `gⱼ`
is already in `(F)` because `π³gⱼ = Fⱼ`. Thus its localization is `Q_π/(F)`.
Adjoin the original variables `x` to this presentation and impose `xᵢ = ξᵢ`.
Eliminating `x` gives `Q_π/(F)`. Alternatively impose `f(x)=0` first, obtaining
`A_π[v,w]/(xᵢ-π²Σₖsᵢₖvₖ-π³wᵢ)`. Since `π³` is a unit, each displayed equation
solves uniquely for `wᵢ`, and elimination identifies the result with `A_π[v]`.
These maps preserve `R`, are mutually inverse on every generator, and also work for
empty sets of variables or relations. Localization commutes with each quotient by
its universal property. The lifted variable indices simply rename the polynomial
ring. -/
theorem desingularization_inverted_quotient_equiv
    (R : Type u) (A : Type w) [CommRing R] [CommRing A] [Algebra R A]
    (π : R) (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m))
    (hc : c ≤ m) (s : Fin n → Fin c → R)
    (g : Fin c → MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R)
    (hg : ∀ j : Fin c,
      aeval (R := R) (fun i : Fin n ↦
        C π ^ 2 * ∑ k, C (s i k) *
          X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inl k)) +
        C π ^ 3 * X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inr i)))
        (P.relation (Fin.castLE hc j)) = C π ^ 3 * g j) :
    let Q := MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R
    let ξ : Fin n → Q := fun i ↦
      C π ^ 2 * ∑ k, C (s i k) * X (ULift.up (Sum.inl k)) +
        C π ^ 3 * X (ULift.up (Sum.inr i))
    let S := Q ⧸ Ideal.span (Set.range g)
    let K := Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range g)))
      (Ideal.span (Set.range (fun j : Fin m ↦ aeval (R := R) ξ (P.relation j))))
    Nonempty (Localization.Away (algebraMap R (S ⧸ K) π) ≃ₐ[R]
      MvPolynomial (Fin c) (Localization.Away (algebraMap R A π))) := by
  sorry

end Algebra
