/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientTwistAnnihilator

/-! # The actual finite quotient coefficients for the structural trace

Source: the coefficient convention and paragraph 2 of the finite exceptional proof.
(blueprint: lem-sf-finite-exceptional-trace-coefficients).
The constructions are the discrete continuous-function rings of the actual quotients.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.NativeFiniteExceptional.TraceCoefficients

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

/-- The actual positive quotient, with index n denoting exponent n+1.
Source: coefficient convention (blueprint: lem-sf-finite-exceptional-trace-coefficients). -/
abbrev Ring (n : ℕ) := Padic.coefficientExtensionRing ell E (n + 1)

local instance (n : ℕ) : TopologicalSpace (Ring ell E n) := ⊥
local instance (n : ℕ) : DiscreteTopology (Ring ell E n) := discreteTopology_bot _
local instance (n : ℕ) : IsTopologicalRing (Ring ell E n) := inferInstance
local instance (n : ℕ) : Finite (Ring ell E n) :=
  Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.succ_pos n)

/-- The discrete quotient as its continuous-function condensed ring.
Source: finite coefficient convention
(blueprint: lem-sf-finite-exceptional-trace-coefficients). -/
def ring (n : ℕ) : ScalarSixRing.{u} := ⟨cartesianFinitePointRing (Ring ell E n)⟩

/-- The quotient factor map, including equal levels.
Source: coefficient reductions (blueprint: lem-sf-finite-exceptional-trace-coefficients). -/
def quotientRing {m n : ℕ} (h : n ≤ m) : Ring ell E m →+* Ring ell E n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- Postcomposition on profinite continuous sections by the actual quotient map.
Source: coefficient reductions (blueprint: lem-sf-finite-exceptional-trace-coefficients). -/
def quotient {m n : ℕ} (h : n ≤ m) : ring ell E m ⟶ ring ell E n :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse (quotientRing ell E h)
        continuous_of_discreteTopology)⟩⟩

end WeilConjectures.NativeFiniteExceptional.TraceCoefficients
