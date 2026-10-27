/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.RealWeilSheaves
public import Sheaf.Paper.AdicLocalCharacteristicFactor
public import Sheaf.Paper.AdicPunctualWeights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

import Sheaf.Algebra.Polynomial.ReciprocalRootFactorization
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant

/-! # Local weights and reality for real Weil sheaves

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-weights
(blueprint: sk-d-real-weights).

The definitions below spell out the local polynomial, logarithmic weight, punctual
purity, upper weight bound, and reality conditions for a finite-dimensional Weil
representation.  The same predicates apply to a constructible Weil sheaf after
replacing the representation by the finite-dimensional stalk and its local
geometric Frobenius.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace RealSheaves

namespace LocalWeights

variable {K : Type u} [Field K] [Finite K]
  {C₀ : Scheme.{u}} {p : C₀ ⟶ Spec (.of K)} [IsCurve p]
  (W : WeilGroup p) {E : Type v} [Field E]
  {V : Type w} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  (ρ : Representation E W.carrier V)

/-- The local factor `det (1 - T ρ(F_x))` at a closed point.
Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-weights
(blueprint: sk-d-real-weights). -/
def localPolynomial (x : C₀.finitePoints) : Polynomial E :=
  (ρ (W.frobenius x)).charpolyRev

/-- The local eigenvalues, counted by algebraic multiplicity.
Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-weights
(blueprint: sk-d-real-weights). -/
def localEigenvalues (x : C₀.finitePoints) : Multiset E :=
  (ρ (W.frobenius x)).charpoly.roots

/-- Punctual purity at weight `w`, quantified over all closed points and eigenvalues.
Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-weights
(blueprint: sk-d-real-weights). -/
def IsPunctuallyPure (ι : E →+* ℂ) (w : ℝ) : Prop :=
  ∀ (x : C₀.finitePoints) (α : E), α ∈ localEigenvalues W ρ x →
    WeilGroup.frobeniusWeight ι (C₀.pointNorm x.1) α = w

/-- The upper weight bound at `w`, quantified over all local eigenvalues.
Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-weights
(blueprint: sk-d-real-weights). -/
def HasWeightsAtMost (ι : E →+* ℂ) (w : ℝ) : Prop :=
  ∀ (x : C₀.finitePoints) (α : E), α ∈ localEigenvalues W ρ x →
    WeilGroup.frobeniusWeight ι (C₀.pointNorm x.1) α ≤ w

/-- Reality of all local polynomials, coefficient by coefficient.
Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-weights
(blueprint: sk-d-real-weights). -/
def IsReal (ι : E →+* ℂ) : Prop :=
  ∀ (x : C₀.finitePoints) (n : ℕ),
    (starRingEnd ℂ) (ι ((localPolynomial W ρ x).coeff n)) =
      ι ((localPolynomial W ρ x).coeff n)

/-- The local spectrum consists of nonzero inverse roots, with their multiplicities.
Source: blueprint sk-d-real-weights, local polynomial and inverse-root clauses
(blueprint: sk-d-real-weights).
Proof: the characteristic polynomial is monic of degree dim(V). It splits over E.
The local group element acts invertibly, hence has nonzero determinant; the constant
coefficient of its characteristic polynomial is its signed determinant, so zero is
not a root. Reverse the monic linear factorization to obtain the product of
(1 - alpha T). For alpha nonzero, the root multiplicity at alpha in the
characteristic polynomial equals the root multiplicity at its inverse in that
product, by lem-weil-reciprocal-root-factorization. This also covers dimension zero,
when both polynomials are 1 and both multiplicities are zero. -/
theorem local_spectral_data [IsAlgClosed E] (x : C₀.finitePoints) :
    (∀ α ∈ localEigenvalues W ρ x, α ≠ 0) ∧
    localPolynomial W ρ x =
      ((localEigenvalues W ρ x).map fun α ↦ 1 - Polynomial.C α * Polynomial.X).prod ∧
    ∀ α : E, α ≠ 0 →
      Polynomial.rootMultiplicity α⁻¹ (localPolynomial W ρ x) =
        Polynomial.rootMultiplicity α (ρ (W.frobenius x)).charpoly := by
  sorry

/-- Reality is exactly stability of the complex eigenvalue multiset, with multiplicities.
Source: blueprint sk-d-real-weights, reality equivalence (blueprint: sk-d-real-weights).
Proof: factor the characteristic polynomial over E. Invertibility of local Frobenius
excludes zero roots. Reversing its monic linear factorization gives the product
of (1 - alpha T). Apply iota and conjugate each factor. The coefficients are real
exactly when that conjugated polynomial is unchanged. Uniqueness of reciprocal-root
factorization (lem-weil-reciprocal-root-factorization) identifies the two multisets;
conversely equal multisets give equal products. This includes rank zero. -/
theorem isReal_iff_conjugation [IsAlgClosed E] (ι : E →+* ℂ) :
    IsReal W ρ ι ↔ ∀ x : C₀.finitePoints,
      ((localEigenvalues W ρ x).map ι).map (starRingEnd ℂ) =
        (localEigenvalues W ρ x).map ι := by
  sorry

end LocalWeights

open WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The pointwise upper logarithmic weight bound on a constructible Weil sheaf.
It quantifies over the actual stalk eigenvalues of def-weil-punctual-weights.
Source: blueprint sk-d-real-weights, final paragraph (blueprint: sk-d-real-weights). -/
def HasConstructibleWeightsAtMost (ι : Qbar →+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) (w : ℝ) : Prop :=
  ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (α : Qbar),
    SfPunctualEigenvalue D l hl Qbar Y₀ F y α →
      WeilGroup.frobeniusWeight ι (Nat.card (Y₀.left.residueField y.val)) α ≤ w

/-- The existing constructible purity predicate has the displayed logarithmic formulation.
Source: blueprint sk-d-real-weights, weight display and constructible clause
(blueprint: sk-d-real-weights).
Proof: local geometric Frobenius is invertible, so its eigenvalues and their images
under the field embedding are nonzero. The residue field has cardinality greater
than one. Taking logarithms of |iota alpha| = q_y^(w/2), and using log(q_y)>0,
gives 2 log |iota alpha| / log(q_y) = w. Conversely exponentiate this equality.
Apply this at every closed point and every finite-stage stalk eigenvalue. -/
theorem constructible_purity_iff_logarithmic (ι : Qbar →+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) (w : ℝ) :
    SfIsPunctuallyPureOfWeight D l hl Qbar Y₀ ι F w ↔
      ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (α : Qbar),
        SfPunctualEigenvalue D l hl Qbar Y₀ F y α →
          WeilGroup.frobeniusWeight ι (Nat.card (Y₀.left.residueField y.val)) α = w := by
  sorry

/-- Constructible reality is stability of the complex local eigenvalue multisets.
The reverse of the local factor is the characteristic polynomial of stalk Frobenius.
Source: blueprint sk-d-real-weights, reality and constructible clauses
(blueprint: sk-d-real-weights).
Proof: choose a finite-stage presentation of the Weil sheaf and a geometric lift
of the closed point. The canonical factor is det(1 - T F_y), and its reverse
is the monic characteristic polynomial because F_y is invertible. Over the
algebraically closed coefficient field its roots are all eigenvalues with their
algebraic multiplicities. Apply the coefficient embedding. Complex conjugation
fixes all polynomial coefficients exactly when it preserves this root multiset:
use unique factorization of a monic polynomial into its linear factors. The
characterization of sfLocalCharacteristicFactor makes this independent of both
choices. For a zero stalk the factor is 1 and the multiset is empty. -/
theorem constructible_reality_iff_conjugation (ι : Qbar →+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) :
    SfIsReal D l hl Qbar Y₀ ι F ↔
      ∀ y : {y : Y₀.left // y ∈ closedPoints Y₀.left},
        (((sfLocalCharacteristicFactor D l hl Qbar Y₀ F y).map ι).reverse.roots).map
          (starRingEnd ℂ) =
        ((sfLocalCharacteristicFactor D l hl Qbar Y₀ F y).map ι).reverse.roots := by
  sorry

end RealSheaves

