/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Order.RelSeries
public import Sheaf.RingTheory.ExcellentRing

/-!
# Affine catenarity and chains of irreducible closed subsets

Source: Stacks Project, Algebra, Tag 02IH (lemma-catenary), using Tags 00ES and 00NI;
Schemes, Tag 01HW (blueprint: lem-trf-affine-catenary-chain-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open TopologicalSpace

namespace AlgebraicGeometry

/-- An affine scheme identifies prime intervals in its global section ring with the
opposite intervals of irreducible closed subsets. Reversing the image of a finite strict
chain preserves its length and saturation. Catenarity is therefore precisely bounded
chain lengths and equal saturated-chain lengths in every irreducible-closed interval.
Bounded lengths also guarantee saturated chains in either type of interval. The empty
scheme has a zero global section ring and neither kind of interval.

Source: Stacks Project, Algebra, Tag 02IH (lemma-catenary), using Tags 00ES and 00NI;
Schemes, Tag 01HW (blueprint: lem-trf-affine-catenary-chain-criterion).

Proof:
1. Use the affine identification in `lem-weil-pbc-affine-open-spec-points` at the top
   open to obtain `h : T ≃ₜ PrimeSpectrum Γ(T, ⊤)`, also when `T` is empty.
2. Inverse image along `h` and image along its inverse preserve closedness,
   nonemptiness and irreducibility (`def-weil-irreducible-components`).
3. Compose this with `PrimeSpectrum.pointsEquivIrreducibleCloseds`, the correspondence
   of `lem-weil-pbc-spec-irreducible-closed-subsets-primes`. It reverses and reflects
   inclusion. Restricting to the entire endpoint intervals gives the asserted order
   isomorphisms, with value the inverse image of the zero locus.
4. Send a chain `r₀ < ⋯ < rₙ` to `F(rₙ) < ⋯ < F(r₀)`. The inverse uses the inverse
   interval bijection and reverses indices again. Both composites are identities,
   including when `n = 0`. An insertion corresponds uniquely to an insertion on the
   other side, since every intermediate element belongs to the full interval.
5. Comparable endpoints admit a singleton chain if equal and a two-term chain otherwise.
   Under a finite bound, the nonempty set of attained lengths has a greatest member.
   Any insertion in a chain of that length contradicts maximality, so it is saturated.
6. Unpack `IsCatenaryRing` from `def-exc-excellent-ring`. The chain bijections transfer
   the bound on all lengths and equality of saturated lengths in both directions.
7. For empty `T`, the sheaf axiom gives a unique global section. The zero ring has no
   prime ideals and the empty space no nonempty irreducible closed subsets. Thus all
   interval assertions are vacuous; equal endpoints elsewhere give length zero. -/
theorem affine_catenary_chain_criterion (T : Scheme.{u}) [IsAffine T] :
    ∃ (h : T ≃ₜ PrimeSpectrum Γ(T, ⊤))
      (F : PrimeSpectrum Γ(T, ⊤) → IrreducibleCloseds T),
      (∀ r : PrimeSpectrum Γ(T, ⊤),
        (F r : Set T) = h ⁻¹' PrimeSpectrum.zeroLocus (r.asIdeal : Set Γ(T, ⊤))) ∧
      (∀ (p q : PrimeSpectrum Γ(T, ⊤)), p ≤ q →
        ∃ e : Set.Icc p q ≃o (Set.Icc (F q) (F p))ᵒᵈ,
          ∀ r : Set.Icc p q, (e r).val = F r.val) ∧
      (∀ (p q : PrimeSpectrum Γ(T, ⊤)), p ≤ q →
        ∃ e : {s : LTSeries (PrimeSpectrum Γ(T, ⊤)) // s.head = p ∧ s.last = q} ≃
            {s : LTSeries (IrreducibleCloseds T) // s.head = F q ∧ s.last = F p},
          ∀ s : {s : LTSeries (PrimeSpectrum Γ(T, ⊤)) // s.head = p ∧ s.last = q},
            (e s).val.length = s.val.length ∧
            (e s).val.toList = (s.val.toList.map F).reverse ∧
            ((∀ i : Fin s.val.length, s.val i.castSucc ⋖ s.val i.succ) ↔
              ∀ i : Fin (e s).val.length,
                (e s).val i.castSucc ⋖ (e s).val i.succ)) ∧
      (IsCatenaryRing Γ(T, ⊤) ↔
        ∀ Z Z' : IrreducibleCloseds T, Z ≤ Z' →
          (∃ N : ℕ, ∀ s : LTSeries (IrreducibleCloseds T),
            s.head = Z → s.last = Z' → s.length ≤ N) ∧
          ∀ s t : LTSeries (IrreducibleCloseds T),
            s.head = Z → s.last = Z' → t.head = Z → t.last = Z' →
            (∀ i : Fin s.length, s i.castSucc ⋖ s i.succ) →
            (∀ i : Fin t.length, t i.castSucc ⋖ t i.succ) → s.length = t.length) ∧
      (∀ Z Z' : IrreducibleCloseds T, Z ≤ Z' →
        (∃ N : ℕ, ∀ s : LTSeries (IrreducibleCloseds T),
          s.head = Z → s.last = Z' → s.length ≤ N) →
        ∃ s : LTSeries (IrreducibleCloseds T), s.head = Z ∧ s.last = Z' ∧
          ∀ i : Fin s.length, s i.castSucc ⋖ s i.succ) ∧
      (∀ p q : PrimeSpectrum Γ(T, ⊤), p ≤ q →
        (∃ N : ℕ, ∀ s : LTSeries (PrimeSpectrum Γ(T, ⊤)),
          s.head = p → s.last = q → s.length ≤ N) →
        ∃ s : LTSeries (PrimeSpectrum Γ(T, ⊤)), s.head = p ∧ s.last = q ∧
          ∀ i : Fin s.length, s i.castSucc ⋖ s i.succ) ∧
      (IsEmpty T → Subsingleton Γ(T, ⊤) ∧ IsEmpty (PrimeSpectrum Γ(T, ⊤)) ∧
        IsEmpty (IrreducibleCloseds T)) := by
  sorry

end AlgebraicGeometry
