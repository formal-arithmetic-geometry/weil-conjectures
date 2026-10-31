/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper rigidity on a single closed lifted test

Source: degree-zero closed-test calculation of compactification coherence, paragraph (2).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  moduleObjectDerivedPushforward moduleObjectDerivedPullback
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ClosedTestDerivedExchangeModel.pull ClosedTestDerivedExchangeModel.sectionsOver
  ClosedTestDerivedExchangeModel.exchange

/-- Proper closed exchange is invertible after evaluation on one lifted w-contractible test.
This is a statement about one derived evaluation, before conservativity and descent.

Source: blueprint latest, compactification coherence refinement, paragraph (2),
steps 1--4 of lem-sfb-proper-constructible-closed-exchange-heart
(blueprint: lem-sfb-proper-constructible-lifted-test-restriction).

Proof: Write W for the specified lift of V, B=Gamma(W,O), and J=Jac(B).
The closed-lift geometry identifies V with Spec(B/IB), with IB contained in J.
Maximal-ideal correspondence gives Jac(B/IB)=J/IB; the third isomorphism theorem
identifies both closed-point fibres with Spec(B/J), compatibly with their maps to W.
These assertions include the zero ring and the empty fibre. Properness is preserved
by base change. Pull back the constructible stratification and its finite scalar
models; scalar-matrix inverse image preserves their presentations. Both sheaves
therefore lie in the weak Serre coproduct closures required by proper closed-fibre
rigidity. Apply that rigidity first to f at W, then to fZ at V. Both canonical maps
to the common closed-point fibre are invertible. Ringed slice localization identifies
derived evaluation with sections after pullback. The composite-adjunction unit
identity and the projection-preserving pullback isomorphisms identify the first
restriction with testRestriction followed by the second. Cancel the second
isomorphism. Apply the normalized nonaffine closed-test exchange identification:
evaluatedExchange followed by its right comparison is the left comparison followed
by testRestriction. Evaluate this identity at M[0] in the bounded-below category.
Both comparison components are invertible, so the evaluated exchange is invertible.
By the definition of evaluatedExchange this is sectionsOver.map of exchange.app M[0].
All coefficient identifications are the original ones, with no scalar extension or Tor bound.
-/
theorem proper_constructible_lifted_test_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))))
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (ClosedTestDerivedExchangeModel.closedMap A I))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)] :
    IsIso ((ClosedTestDerivedExchangeModel.sectionsOver Λ V.hom).map
      ((ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
