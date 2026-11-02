/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting

/-! # The four condensed coefficient stages in the Poincare setting

Source: latest blueprint sk-def-set and its fixed sk-def-sf-setting.
The geometric model is the existing PoincareDualitySetting, which does not assume properness.
(blueprint: sk-def-set)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedPoincare

open PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- The four stages fixed in the Poincare chapter; these are presentation indices,
not replacement rings. Source: coefficient list (blueprint: sk-def-set). -/
inductive Stage where
  | finite
  | integral
  | rational
  | closure

/-- The specified uniformizer quotient is finite.
Source: Serre, Local Fields II.2; finite coefficient stage (blueprint: sk-def-set).
Proof: the integer ring is a DVR with finite residue field. Its maximal ideal is
(π). The successive quotients (π)^j/(π)^(j+1) are one-dimensional over the residue
field, so induction on n makes O_E/(π)^n finite; n=0 is the zero ring. -/
theorem residueFinite (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) : Finite (PadicAlgCl.integers ell E ⧸ (Ideal.span ({π} : Set _)) ^ n) := by
  sorry

/-- A rational-prime power annihilates the specified quotient, without identifying
it with the different quotient by ell^n.
Source: Serre, Local Fields II.2; admissible finite stage (blueprint: sk-def-set).
Proof: ell lies in the maximal ideal (π), hence ell^(n+1) lies in (π)^(n+1), which
is contained in (π)^n. Its image in the quotient is therefore zero, including n=0. -/
theorem residueAnnihilator (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) :
    (ell ^ (n + 1) : PadicAlgCl.integers ell E ⧸ (Ideal.span ({π} : Set _)) ^ n) = 0 := by
  sorry

/-- Select the existing actual coefficient presentation at the chosen one of four stages.
The finite ring is exactly O_E/(π)^n, with its discrete condensed realization.
Source: fixed coefficient data (blueprint: sk-def-set). -/
def coefficient (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) (_hn : 1 ≤ n) : Stage → Coefficient ell
  | .finite => .finite
      (.of (PadicAlgCl.integers ell E ⧸ (Ideal.span ({π} : Set _)) ^ n))
      (residueFinite ell E π hπ n) n (residueAnnihilator ell E π hπ n)
  | .integral => .integral E
  | .rational => .rational E
  | .closure => .closure

/-- The geometric datum and the choice of one of the four fixed coefficient stages.
The distinct primes, closure, finite subextension, uniformizer and positive exponent
are the surrounding parameters; there is no properness or ambient adjoint assumption.
Source: latest blueprint sk-def-set, all setting clauses (blueprint: sk-def-set). -/
structure Setting (D : WeilConjectures.FiniteFieldDatum.{u})
    (_hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) (_hn : 1 ≤ n) (d : ℕ) where
  geometry : PoincareDualitySetting D.k₀ d
  stage : Stage

end AlgebraicGeometry.ProEtale.CondensedPoincare
