/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.CompleteLocalQuotient

/-! # Convergent lifting of split-node coordinates

Source: Stacks Project, Curves, Tag 0CBX (lemma-formal-local-structure-nodal-family),
second paragraph and the induction and limits in the third paragraph
(blueprint: lem-trf-split-node-coordinate-lifting).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace IsLocalRing

/-- Coordinates of a split nodal special fibre admit successive corrections with a
product in the base ring, converging in the maximal-ideal-adic topologies.

Source: Stacks Project, Curves, Tag 0CBX (lemma-formal-local-structure-nodal-family),
second and third proof paragraphs (blueprint: lem-trf-split-node-coordinate-lifting).

The coefficient identity `hθ` expresses that the ring equivalence is an isomorphism
of algebras over `A ⧸ maximalIdeal A`, with the canonical action on the special fibre.
Index `r` of each sequence here denotes index `r + 1` in the source.

Proof:
1. Put I = mB. The two special-fibre coordinates are nonunits, so their arbitrary
lifts lie in n. Their product lies in I, giving the initial approximation h = 0.
2. Partition the nonconstant monomials of a two-variable series into those divisible
by x and the remaining ones divisible by y. Thus every b in B has an expression
b = α(a) + up + vq + ε with ε in I, by the given special-fibre equivalence.
3. Given δ = uv - α(h) in m^s B, write δ = ∑ α(fᵢ)bᵢ with fᵢ in m^s, and apply
step 2 to every bᵢ. Set P = ∑ α(fᵢ)pᵢ, Q = ∑ α(fᵢ)qᵢ, d = ∑ fᵢaᵢ. Replacing
(u,v,h) by (u-Q,v-P,h+d) leaves error ∑ α(fᵢ)εᵢ + QP in m^(s+1)B, since
2s ≥ s+1. The differences have the asserted orders, preserving all reductions
and maximal-ideal memberships. Recursively choose these corrections.
4. Telescoping gives stabilization modulo every n^N in B and m^N in A, because
m^N B is contained in n^N. The assumed adic completeness gives limits u,v,h;
reduction modulo the maximal ideals puts u,v in n and h in m.
5. By lem-weil-pbc-complete-local-quotient (Stacks Tag 0325), B/I is complete local
and hence separated. The reduction of u-u₁, and likewise v-v₁, lies in every
power of its maximal ideal, so vanishes. The limits retain the prescribed lifts.
6. For every N, compare uv - α(h) with the s-th approximation for s ≥ N. The
product differences, α(h-h_s), and the approximation error all lie in n^N.
Separatedness of B forces uv = α(h). No I-adic completeness of B is used. -/
theorem exists_split_node_coordinate_lifting
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    (α : A →+* B)
    (hα : ∀ a : A, a ∈ maximalIdeal A → α a ∈ maximalIdeal B)
    (θ : (MvPowerSeries (Fin 2) (A ⧸ maximalIdeal A) ⧸
      Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (A ⧸ maximalIdeal A)) *
        MvPowerSeries.X 1}) ≃+* (B ⧸ (maximalIdeal A).map α))
    (hθ : ∀ a : A,
      θ (Ideal.Quotient.mk _ (MvPowerSeries.C (Ideal.Quotient.mk (maximalIdeal A) a))) =
        Ideal.Quotient.mk ((maximalIdeal A).map α) (α a))
    (u₁ v₁ : B)
    (hu₁ : Ideal.Quotient.mk ((maximalIdeal A).map α) u₁ =
      θ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)))
    (hv₁ : Ideal.Quotient.mk ((maximalIdeal A).map α) v₁ =
      θ (Ideal.Quotient.mk _ (MvPowerSeries.X 1))) :
    ∃ (us vs : ℕ → B) (hs : ℕ → A) (u v : B) (h : A),
      us 0 = u₁ ∧ vs 0 = v₁ ∧ hs 0 = 0 ∧
      (∀ r : ℕ,
        us r ∈ maximalIdeal B ∧ vs r ∈ maximalIdeal B ∧ hs r ∈ maximalIdeal A ∧
        Ideal.Quotient.mk ((maximalIdeal A).map α) (us r) =
          θ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) ∧
        Ideal.Quotient.mk ((maximalIdeal A).map α) (vs r) =
          θ (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) ∧
        us r * vs r - α (hs r) ∈ (maximalIdeal A ^ (r + 1)).map α ∧
        us (r + 1) - us r ∈ (maximalIdeal A ^ (r + 1)).map α ∧
        vs (r + 1) - vs r ∈ (maximalIdeal A ^ (r + 1)).map α ∧
        hs (r + 1) - hs r ∈ maximalIdeal A ^ (r + 1)) ∧
      (∀ N : ℕ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
        us r - u ∈ maximalIdeal B ^ N ∧
        vs r - v ∈ maximalIdeal B ^ N ∧ hs r - h ∈ maximalIdeal A ^ N) ∧
      u ∈ maximalIdeal B ∧ v ∈ maximalIdeal B ∧ h ∈ maximalIdeal A ∧
      Ideal.Quotient.mk ((maximalIdeal A).map α) u =
        θ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) ∧
      Ideal.Quotient.mk ((maximalIdeal A).map α) v =
        θ (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) ∧
      u * v = α h := by
  sorry

end IsLocalRing
