/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
import WeilConjectures.FieldTheory.PBasisExtension

/-!
# Existence of a p-basis

Source: Stacks Project, More on Algebra, Definition 07P1 and Lemma 07P2, applied to the extension
from the prime field.

The p-basis is written inline in the form of
(`KaehlerDifferential.exists_basis_differentials_of_pBasis`) with base field the prime
field `ZMod p`: `k^p = (ZMod p) k^p` is `IntermediateField.adjoin (ZMod p) (Set.range (· ^ p))`.
The prime-field algebra structure is Mathlib's `ZMod.algebra`, registered locally as in
`WeilConjectures.FieldTheory.IntersectionSubfieldsDifferentials`.
-/

@[expose] public section

universe u

attribute [local instance] ZMod.algebra

namespace Field

/-- Every field of prime characteristic has a p-basis over its subfield of p-th powers, written
as a basis of `k` over `IntermediateField.adjoin (ZMod p) (Set.range (· ^ p))` indexed by
exponent vectors with entries `< p`.
Source: Stacks Project, More on Algebra, Definition 07P1 and Lemma 07P2. -/
theorem exists_p_basis (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] :
    ∃ (I : Type u) (t : I → k)
      (b : Module.Basis {E : I →₀ ℕ // ∀ i : I, E i < p}
        (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k),
      ∀ E, b E = E.val.prod (fun i e => t i ^ e) := by
  let I := Empty
  let x : I → k := fun i => i.elim
  have hx : LinearIndependent
      (IntermediateField.adjoin (ZMod p) (Set.range (fun a : k => a ^ p)))
      (fun E : {E : I →₀ ℕ // ∀ i : I, E i < p} =>
        E.val.prod (fun i e => x i ^ e)) := by
    rw [linearIndependent_iff]
    intro l hl
    apply Finsupp.ext
    intro E
    have hE : E = ⟨0, by intro i; exact i.elim⟩ := by
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      exact i.elim
    subst hE
    let z : {E : I →₀ ℕ // ∀ i : I, E i < p} :=
      ⟨0, by intro i; exact i.elim⟩
    have hlz : l = Finsupp.single z (l z) := by
      apply Finsupp.ext
      intro E
      have hEz : E = z := by
        apply Subtype.ext
        apply Finsupp.ext
        intro i
        exact i.elim
      subst E
      simp
    rw [hlz] at hl
    simpa [Finsupp.linearCombination_single] using hl
  obtain ⟨J, y, b, hb⟩ := FieldTheory.exists_pBasis_extension (k := ZMod p) (K := k)
    (p := p) x hx
  refine ⟨Empty ⊕ J, Sum.elim (fun i : Empty => i.elim) y, ?_, ?_⟩
  · exact b
  · exact hb


end Field
