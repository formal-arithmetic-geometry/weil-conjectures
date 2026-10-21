/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.IntegralStratifiedPerfectModels
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility

/-! # The completed local perfect criterion
Source: Bhatt--Scholze, Proposition 6.6.11.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The completed reduction-tower category has the local perfect description.
This is Proposition 6.6.11 alone, before the cohomology characterization of 6.8.11(3).
Source: Bhatt--Scholze, Proposition 6.6.11, with Definition 6.5.1;
(blueprint: lem-weil-pbc-integral-completed-local-perfect-criterion).

Proof: exact immersion inverse image and slice restriction preserve the completed
coefficient ring, reductions, and the Roos completion unit. Finite-stratum and cover
zero detection therefore detect completeness. A bounded finite-projective constant
model is complete: each term is a finite free summand, its quotient tower is
surjective, and the kernel of 1-shift on the product is that summand of the completed
ring. Choose finitely many cover pieces on each quasi-compact stratum to bound all
finite reductions. Their finite cohomology is locally constant. Normalized local
constructible effectivity produces the uniform tower. Finite-ring derived origin
supplies the etale origins; bounded-below full faithfulness lifts the normalization
maps and their inverses uniquely. Faithfulness gives their cocycle equations.
Conversely, the uniform tower bounds the residue reduction, and its finite lisse
cohomology descends to a bounded constructible etale complex. Refine finitely many
constructibility stratifications and make this residue complex locally constant.
The residue ring is a field, so its bounded finite cohomology gives perfect models.
The integral valuation ring is adically complete: compatible residues are Cauchy,
converge in the closed unit ball of the complete finite extension, and have unique
limit since the intersection of uniformizer powers is zero. Completeness restricts
to every stratum. Residue-lisse perfect lifting then gives the required perfect
integral local models. All coefficients here are the actual inverse-image completed
rings, and all etale origins retain the normalization compatibility. -/
theorem integralCompletedLocalPerfectCriterion
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤)))
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
      IsIntegralStratifiedPerfect T (pbcIntegralDatum l E) K := by sorry

end AlgebraicGeometry.Scheme
