/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceChernTwistExistence
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Normalized.NormalizedKummerReduction
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernScalarUnit
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Normalized.NormalizedChernFiniteBoundary
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.KummerLineTwisting

/-! # Normalized Chern data over an arbitrary coefficient field

Source: latest blueprint tower geometric classes, clauses (1)--(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
open DiagonalTrace

/-- Integral Kummer reduction extends to normalized Chern and twist data over E.

Source: latest blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clauses (1)--(2).
(blueprint: lem-sp-tower-class-chern-twist-existence).

Proof: the literal roots and power-unit systems form the Kummer short exact
sequence. Apply simultaneous normalized integral quotient reduction. Extend
along the actual quotient-ring map R to A, using the normalized scalar-unit
comparison induced by the adjunction. The two integral comparisons and this
scalar comparison give the three Chern normalization equations. The normalized
finite-boundary theorem supplies finite Chern normalization. The Kummer root
line is locally free of rank one; its scalar extension yields the exact
positive-tensor/negative-Hom equivalence with its canonical section formulas.
The coefficient map and the argument apply equally to ramified E. -/
theorem exists_normalizedChernTwist (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤))) :
    ∃ c : Chern l E T, c.Normalized l E ∧ FiniteChernNormalization l E c ∧
      Nonempty (Twisting l E c) := by
  let k := kummerData l T hT
  obtain ⟨r, M, i, a, b, ha, hb⟩ := exists_normalizedKummerReduction l T hT k
  obtain ⟨s⟩ := (WeilConjectures.SemilinearSections.semilinearScalarData.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T)
    (fun n ↦ (Rrings l T).obj (op n))
    (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
    (SpTowerClasses.coefficientMap l E T)
    (SpTowerClasses.coefficientMap_transition l E T)).1
  obtain ⟨e, he⟩ := exists_normalizedScalarUnit l E T s
  let c : Chern l E T :=
    { kummer := k
      reduction := r
      rootModule := M
      rootForget := i
      unitIso := a
      rootIso := b
      scalar := s
      scalarUnit := e }
  have hc : c.Normalized l E := ⟨ha, hb, he⟩
  exact ⟨c, hc, finiteChernNormalization_of_normalized l E c hc,
    nonempty_kummerLineTwisting l E T hT c⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
