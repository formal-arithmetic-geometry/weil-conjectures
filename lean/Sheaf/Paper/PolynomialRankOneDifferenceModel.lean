/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.PolynomialRankOneDifferenceModelData
import Sheaf.Paper.PolynomialRankOneSystemExistence
import Sheaf.Paper.PolynomialRankOnePresentation

/-! # Finite polynomial stages and rank-one translation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
open Profinite.CondensedAction.IndUnipotent
open Profinite.CondensedAction.ContinuousRepresentation
open Profinite.CondensedAction.PrimeToEll
open scoped TensorProduct
namespace Profinite.CondensedAction.PolynomialRankOne

variable (ℓ : ℕ) [Fact ℓ.Prime] (k m : ℕ)

/-- Finite polynomial stages give the specified ind-unipotent system and its normalized
internal colimit presentation for both allowed coefficient fields.
Source: latest direct-image stability proof (3), expanded polynomial obligation
(blueprint: lem-sfb-polynomial-rank-one-difference-model).

Proof:
1. Monomials of total degree at most n are finite: every exponent is at most n.
Their coefficient vectors give the basis and identify the stage with its stated span.
The next-stage embedding is injective and every monomial occurs at some stage.
2. Expand each (y_i-u_i)^a by add_pow (lem-pur-commutative-ring-binomial-expansion).
Degree cannot increase. Successive substitutions add parameters; negative parameters
supply inverses. This proves the representation law and transition equivariance.
3. Matrix entries are polynomials in the parameters, hence continuous. The finite
basis topology is the norm topology by lem-sfb-finite-dimensional-linear-map-continuous;
finite sums and products give joint continuity.
4. The monomial formula for def-weil-pbc-polynomial-partial-derivative gives falling
factorials for powers of -d/dy_1. The (n+1)-st power vanishes. This operator commutes
with transitions and translations in the other variables.
5. Divide falling factorials by j! in characteristic zero. The binomial theorem gives
the finite Taylor formula and hence the exponential identity in the existing System.
6. Tensor the monomial basis with F. Its product topology identifies all continuous
sections with finite tuples of continuous F-valued functions. The coefficient
projections and monomial injections give the finite internal coproduct isomorphism,
using def-weil-pbc-internal-abelian-sheaf-module-equivalence.
7. Translation matrices over F intertwine these maps for every varying continuous
parameter. The existing continuous-representation condensation gives P and its exact
tensor transition formulas; completeness of F is never used.
8. The internal coproduct universal property makes the union of finite sub-sums a
colimit. Its compatible translation actions induce the colimit action, and uniqueness
makes the colimit isomorphism equivariant, preserving every monomial coprojection.
This uses only the categorical creation part of
lem-sfb-profinite-action-filtered-colimit-creation, not a sectionwise-colimit formula.
9. Compatible stage derivatives induce D; its monomial formula is -d/dy_1. The finite
stage exponentials induce expD and equal translation by 1. Subtract identity to get
Delta and its finite monomial formula. Constants at n=0, k=0 (r=1), and m=0 obey the
same formulas. No infinite Taylor sum, uniform degree bound, or completion occurs.
-/
theorem polynomial_rank_one_difference_model
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (E₀ : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E₀] :
    ∃ Q : PolynomialSystem ℓ E₀ k m,
      PresentationAssertion ℓ E₀ k m E₀ Q ∧ PresentationAssertion ℓ E₀ k m Ω Q := by
  obtain ⟨Q⟩ := exists_polynomial_system ℓ E₀ k m
  refine ⟨Q, presentation_assertion ℓ E₀ k m E₀ Q ?_,
    presentation_assertion ℓ E₀ k m Ω Q ?_⟩
  · exact continuous_algebraMap E₀ E₀
  · exact continuous_subtype_val

end Profinite.CondensedAction.PolynomialRankOne
