/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod
import WeilConjectures.RingTheory.PBasisComplementMonomialBasis
import WeilConjectures.RingTheory.PowerSeriesResidueMonomialBasis
import Mathlib.Data.Fintype.EquivFin

/-!
# A finite basis containing one for the p-basis coefficient subring

The bounded `p`-basis and variable monomials give a finite basis, containing `1`, of a
power-series polynomial ring over its `p`-basis coefficient subring.

## Implementation details

The cases `J` empty and `n = 0` or `m = 0` are included, using the empty monomial.

## References

* [Stacks, Tag 07P5] (finiteness paragraph of the proof)
-/

@[expose] public section

set_option autoImplicit false

universe u w

attribute [local instance] ZMod.algebra

namespace RingTheory

/-- The bounded p-basis and variable monomials give a finite basis containing one. -/
theorem powerSeriesSubringFiniteBasis
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e => t i ^ e))
    (n m : ℕ) (J : Finset I) (kJ : Subfield k)
    (hkJ : kJ = Subfield.closure
      (Set.range (fun x : k => x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x}))
    (S : Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hS : ∀ f, f ∈ S ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ∈ kJ ∧
        (MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j))) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) S
      (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) (i : Fin d), b i = 1 := by
  classical
  obtain ⟨b, hb⟩ := pBasisComplementMonomialBasis p k I t hpb J kJ hkJ
  obtain ⟨B, hB⟩ := powerSeriesResidueMonomialBasis p (Fact.out : p.Prime).pos
    k kJ (J → Fin p) b n m S hS
  let z : Fin p := ⟨0, (Fact.out : p.Prime).pos⟩
  let q : (J → Fin p) × (Fin n → Fin p) × (Fin m → Fin p) :=
    (fun _ ↦ z, fun _ ↦ z, fun _ ↦ z)
  have hb0 : b (0 : J → Fin p) = 1 := by
    rw [hb]
    simp
  have hbq : b q.1 = 1 := by
    rw [show q.1 = (0 : J → Fin p) by ext x; simp [q, z]]
    exact hb0
  have hB0 : B q = 1 := by
    rw [hB]
    rw [hbq]
    simp [q, z]
  let e := Fintype.equivFin ((J → Fin p) × (Fin n → Fin p) × (Fin m → Fin p))
  refine ⟨_, B.reindex e, e q, ?_⟩
  simpa using hB0

end RingTheory
