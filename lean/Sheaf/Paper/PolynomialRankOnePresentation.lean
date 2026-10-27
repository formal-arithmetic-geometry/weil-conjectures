/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.PolynomialRankOneDifferenceModelData

/-! The internal presentation associated to a finite polynomial system. -/

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

/-- Every finite polynomial system has its normalized internal presentation after
continuous scalar extension compatible with Q_ell.
Source: latest blueprint, direct-images proof (3), expanded proof of
lem-sfb-polynomial-rank-one-difference-model, steps 6--9
(blueprint: lem-sfb-polynomial-rank-one-presentation).

Proof: form the continuous group homomorphism pi by putting the H coordinate first
and the residual coordinates afterward. Its displayed coordinate equation follows
from Fin.cases. Apply IndUnipotent.exists_presentation to Q.system and the continuous
coefficient inclusion. At each stage tensor Q.basis with F. The tensor-polynomial
map sends this basis to the same monomials over F, so coefficient extraction is its
inverse in finite coordinates. These maps and their inverses are continuous for the
finite product module topology, even when F is not complete.

The equivalence between internal modules and sectionwise module sheaves turns these
finite coordinates into the monomial injections j and coefficient projections p.
Their two matrix identities make j a coproduct cocone. Define w by the finite sum
of T's corresponding monomial coprojections. Q.translation and the scalar tower
identify the scalar-extended action with substitution over F. T.translation then
shows w is equivariant, including for varying continuous group parameters. The
section formulas for j and p are the coordinate definitions. Q.inclusion and the
specified transitions of the presentation prove compatibility of w.

Use categorical filtered-colimit creation for internal profinite group actions to
form c, with its underlying-module colimit. The increasing finite subsets of all
monomials exhaust the monomial set: an exponent enters at its total degree. Thus
the compatible w induce an isomorphism from c to the inflated T. To construct its
inverse, send each monomial coprojection into any stage containing that monomial;
transition compatibility makes this independent of the stage. The two coproduct
and colimit universal properties show the composites are identity and give the
normalization equation. No sectionwise formula for the infinite colimit is used.

The compatible scalar-extended derivatives induce D. On monomial coprojections its
formula is minus the first partial derivative, by Q.derivative and Q.monomials.
Differentiation commutes with every translation, so D is an equivariant map. Let
expD be the action of the central element (1,generator ell), and put delta=expD-1.
The finite exponential formula of Q.system gives its specified stage action; the
monomial translation formula gives delta's finite difference formula. Linearity
gives the equation for delta on arbitrary sections. These constructions verify
every clause of PresentationAssertion. Constants, empty residual and spectator
families, and the empty test space obey the same finite formulas. -/
theorem presentation_assertion
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (k m : ℕ) (F : Type u) [NormedField F] [NormedAlgebra ℚ_[ℓ] F]
    [Algebra E F] [IsScalarTower ℚ_[ℓ] E F]
    (Q : PolynomialSystem ℓ E k m) (hf : Continuous (algebraMap E F)) :
    PresentationAssertion ℓ E k m F Q := by
  sorry

end Profinite.CondensedAction.PolynomialRankOne
