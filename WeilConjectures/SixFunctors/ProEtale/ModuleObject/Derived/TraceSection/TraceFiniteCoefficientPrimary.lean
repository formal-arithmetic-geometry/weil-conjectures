/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Positive finite coefficient stages are ell-primary

Source: finite coefficient conventions used in Step 3(d) of the latest blueprint,
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/
lem-trf-trace-class-diagonal-pairing.proof.md.
(blueprint: lem-trf-positive-coefficient-primary).

Ring is just the existing quotient at level n+1 with its finite discrete topology.
-/

@[expose] public noncomputable section
set_option autoImplicit false
namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceSection

/-- The positive coefficient stage; n indexes the level n+1.
Source: finite conventions and Step 3(d) (blueprint: lem-trf-positive-coefficient-primary). -/
def Ring (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) : Type :=
  Padic.coefficientExtensionRing ell E (n + 1)

/-- The existing quotient ring structure.
Source: finite conventions (blueprint: lem-trf-positive-coefficient-primary). -/
instance ringCommRing (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    CommRing (Ring ell E n) := inferInstanceAs (CommRing
      (Padic.coefficientExtensionRing ell E (n + 1)))

/-- Finite coefficients carry their discrete topology.
Source: finite conventions (blueprint: lem-trf-positive-coefficient-primary). -/
instance ringTopology (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    TopologicalSpace (Ring ell E n) := ⊥

/-- Discreteness of the specified finite coefficient topology.
Source: finite conventions (blueprint: lem-trf-positive-coefficient-primary). -/
instance ringDiscrete (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    DiscreteTopology (Ring ell E n) := ⟨rfl⟩

/-- The discrete quotient is a topological ring.
Source: finite conventions (blueprint: lem-trf-positive-coefficient-primary). -/
instance ringTopologicalRing (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    IsTopologicalRing (Ring ell E n) := DiscreteTopology.topologicalRing

/-- The existing positive-level finiteness theorem.
Source: finite conventions (blueprint: lem-trf-positive-coefficient-primary). -/
instance ringFinite (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    Finite (Ring ell E n) := Padic.finite_coefficientExtensionRing ell E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))

/-- The finite coefficient stage is killed by a power of ell.
Source: finite conventions (blueprint: lem-trf-positive-coefficient-primary).
Proof: ell belongs to the maximal ideal of the valuation ring. The chosen uniformizer
spans that ideal, so ell^(n+1) belongs to its (n+1)-st power. Its quotient class is zero,
and multiplication by an arbitrary quotient element gives the asserted nsmul. -/
theorem ringTorsion (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    ∃ m : ℕ, ∀ a : Ring ell E n, (ell ^ m) • a = 0 := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.TraceSection
