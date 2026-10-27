/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Order.RelSeries
public import Mathlib.Order.Cover

/-!
# Irreducible-closed intervals in overlapping open subspaces

Source: Stacks Project, Topology, Tag 02I2 (lemma-catenary), restriction/closure
correspondence in the proof, restricted to endpoint intervals.
(blueprint: lem-trf-overlapping-open-irreducible-intervals)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace TopologicalSpace.IrreducibleCloseds

/-- The full intervals of irreducible closed subsets in overlapping opens correspond by
restriction and closure, including their strict and saturated finite chains.
Source: Stacks Project, Topology, Tag 02I2 (lemma-catenary), proof.
(blueprint: lem-trf-overlapping-open-irreducible-intervals)

Here `A,B` are the restrictions of `Z,Z'` to `U ⊓ V`, and `C,C'` their closures in `U`.
The maps `e`, `rV`, and `rU` are order isomorphisms of the entire endpoint intervals.
The last clause treats strict chains when `saturated = false` and saturated chains when
`saturated = true`. A `RelSeries` of length `n` has `n` strict inclusions and `n+1` terms.
The equivalences are specified termwise by equality of their lists of members; both the
forward and inverse formulas are given. Fixing `n` expresses length preservation and,
by nonemptiness of equivalent types, equality of the attainable lengths in both cases.
Covering inside the full interval is equivalent to covering in the ambient order: any
member inserted between two interval members also lies between its endpoints.

Proof:
1. The intersection `W = U ⊓ V` is open in both subspaces. Apply
   `orderIsoOfIsOpenEmbedding` to its inclusion in `V`. Nonemptiness of `Z ∩ U`
   gives irreducible closed restrictions `A ≤ B` whose closures in `V` are `Z,Z'`.
   Apply the same correspondence to `W` inside `U` to obtain `C ≤ C'`, with the
   asserted restrictions back to `W`.
2. Restrict the `V` correspondence to the whole interval `[Z,Z']`. Every member
   meets `W` because it contains `Z`; conversely closure of any member of `[A,B]`
   lies between the closures `Z,Z'`. The inverse identities and inclusion preservation
   give `rV` onto the full interval `[A,B]`.
3. Repeat for `U`: every member of `[C,C']` meets `W` because it contains `C`.
   This gives `rU`. Set `e = rV.trans rU.symm`. The two inverse identities for each
   restriction cancel in the composites, giving both closure formulas, the commuting
   restriction identity, and all four endpoint equalities.
4. Apply `e` to each term of a finite strict chain. Inclusion is preserved and equality
   is reflected, so the chain stays strict and its length is unchanged. Applying `e.symm`
   termwise is inverse, also for length zero when the endpoints coincide.
5. Any insertion between adjacent image members pulls back under `e.symm` to an insertion
   between the original members, and conversely. Such insertions stay inside the full
   endpoint intervals. Hence the termwise maps restrict to inverse bijections on saturated
   chains of each length. No separation, sobriety, or finiteness assumption was used. -/
theorem overlappingOpenIrreducibleIntervals
    {X : Type u} [TopologicalSpace X] (U V : Opens X)
    (Z Z' : IrreducibleCloseds V) (hZZ' : Z ≤ Z')
    (hmeet : ((Z : Set V) ∩ Subtype.val ⁻¹' (U : Set X)).Nonempty) :
    ∃ (C C' : IrreducibleCloseds U) (hCC' : C ≤ C')
      (A B : IrreducibleCloseds ↥(U ⊓ V)) (hAB : A ≤ B),
      (C : Set U) = closure (Subtype.val ⁻¹' (Subtype.val '' (Z : Set V))) ∧
      (C' : Set U) = closure (Subtype.val ⁻¹' (Subtype.val '' (Z' : Set V))) ∧
      (A : Set ↥(U ⊓ V)) =
        (fun x : ↥(U ⊓ V) ↦ (⟨x.val, x.property.2⟩ : V)) ⁻¹' (Z : Set V) ∧
      (B : Set ↥(U ⊓ V)) =
        (fun x : ↥(U ⊓ V) ↦ (⟨x.val, x.property.2⟩ : V)) ⁻¹' (Z' : Set V) ∧
      (fun x : ↥(U ⊓ V) ↦ (⟨x.val, x.property.1⟩ : U)) ⁻¹' (C : Set U) = A ∧
      (fun x : ↥(U ⊓ V) ↦ (⟨x.val, x.property.1⟩ : U)) ⁻¹' (C' : Set U) = B ∧
      ∃ (e : Set.Icc Z Z' ≃o Set.Icc C C')
        (rV : Set.Icc Z Z' ≃o Set.Icc A B) (rU : Set.Icc C C' ≃o Set.Icc A B),
        (∀ D : Set.Icc Z Z', ((e D).val : Set U) =
          closure (Subtype.val ⁻¹' (Subtype.val '' (D.val : Set V)))) ∧
        (∀ E : Set.Icc C C', ((e.symm E).val : Set V) =
          closure (Subtype.val ⁻¹' (Subtype.val '' (E.val : Set U)))) ∧
        (∀ D : Set.Icc Z Z', ((rV D).val : Set ↥(U ⊓ V)) =
          (fun x : ↥(U ⊓ V) ↦ (⟨x.val, x.property.2⟩ : V)) ⁻¹' (D.val : Set V)) ∧
        (∀ E : Set.Icc C C', ((rU E).val : Set ↥(U ⊓ V)) =
          (fun x : ↥(U ⊓ V) ↦ (⟨x.val, x.property.1⟩ : U)) ⁻¹' (E.val : Set U)) ∧
        (∀ T : Set.Icc A B, ((rV.symm T).val : Set V) =
          closure ((fun x : ↥(U ⊓ V) ↦ (⟨x.val, x.property.2⟩ : V)) '' (T.val : Set _))) ∧
        (∀ T : Set.Icc A B, ((rU.symm T).val : Set U) =
          closure ((fun x : ↥(U ⊓ V) ↦ (⟨x.val, x.property.1⟩ : U)) '' (T.val : Set _))) ∧
        (∀ D : Set.Icc Z Z', rU (e D) = rV D) ∧
        e ⟨Z, le_rfl, hZZ'⟩ = ⟨C, le_rfl, hCC'⟩ ∧
        e ⟨Z', hZZ', le_rfl⟩ = ⟨C', hCC', le_rfl⟩ ∧
        e.symm ⟨C, le_rfl, hCC'⟩ = ⟨Z, le_rfl, hZZ'⟩ ∧
        e.symm ⟨C', hCC', le_rfl⟩ = ⟨Z', hZZ', le_rfl⟩ ∧
        (∀ (saturated : Bool) (n : ℕ),
          ∃ ec :
            {s : RelSeries {p : Set.Icc Z Z' × Set.Icc Z Z' |
                if saturated then p.1 ⋖ p.2 else p.1 < p.2} //
              s.head.val = Z ∧ s.last.val = Z' ∧ s.length = n} ≃
            {s : RelSeries {p : Set.Icc C C' × Set.Icc C C' |
                if saturated then p.1 ⋖ p.2 else p.1 < p.2} //
              s.head.val = C ∧ s.last.val = C' ∧ s.length = n},
            (∀ s, (ec s).val.toList = s.val.toList.map e) ∧
            (∀ t, (ec.symm t).val.toList = t.val.toList.map e.symm)) := by
  sorry

end TopologicalSpace.IrreducibleCloseds
