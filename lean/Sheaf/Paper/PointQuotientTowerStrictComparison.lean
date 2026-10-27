/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.IntegralCoefficientPresentationComparison
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv

/-! # The strict coefficient-presentation comparison of quotient towers

Source: clause (3) of the proof of prop-trf-rational-frobenius-integral-model,
step 7 of lem-trf-point-quotient-tower-homotopy. This comparison is before sections
and before derived localization, and applies to every complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PointQuotientTower

/-- The normalized coefficient isomorphisms identify the entire strict towers.
Source: clause (3) of prop-trf-rational-frobenius-integral-model, step 7 of
lem-trf-point-quotient-tower-homotopy
(blueprint: lem-trf-point-quotient-tower-strict-comparison).

Proof: at degree i and level n send b tensor x to e_n(b) tensor x, where e_n
is IntegralCoefficientPresentation.level. The projection equation for e makes
this map balanced over the completed coefficient ring, after restricting the
input along e.hom and the output along e.inv. Use the inverse level isomorphism
to construct the reverse balanced map. The composites fix pure tensors and thus
are identities after sheafification. Naturality of these maps in the input
module makes them commute with every differential. The quotient compatibility
of the normalized family q, supplied by IntegralCoefficientPresentation.comparison,
gives e_n rho = rho e_(n+1); applying this equation to b tensor x shows that the
maps and their inverses commute with adjacent quotient transitions. Every arrow
of the inverse sequence is a composite of adjacent arrows, so these are inverse
maps of strict towers in each degree, and hence an isomorphism of complexes of
towers. The displayed generator equation is exactly their construction. This
argument applies to an arbitrary complex, including zero and unbounded ones;
it uses neither a K-flat hypothesis nor a derived counit. -/
theorem strictPresentationComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u})
    (q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (hq : ∀ (n : ℕ) (x : PbcIntegralRing l E), q n (Ideal.Quotient.mk _ x) =
      ULift.up (Ideal.Quotient.mk _ x.down))
    (e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E T)
    (he : ∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
      pbcAdicProjection T (pbcIntegralDatum l E) n ≫
        (IntegralCoefficientPresentation.level l E T q n).hom)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    ∃ r :
      (((pbcRestrict e.hom).mapHomologicalComplex (.up ℤ) ⋙
        completedReductionComplexTowerFunctor T (pbcIntegralDatum l E) ⋙
          ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict e.inv)).mapHomologicalComplex
            (.up ℤ)).obj P) ≅
      (((Functor.ofOpSequence
        (X := fun n ↦ unrestrictedIntegralComplexFunctor l E T n)
        (unrestrictedIntegralTransition l E T)).flip ⋙
          (HomologicalComplex.functorEquivalence
            (integralTowerModules l E T) (.up ℤ) ℕᵒᵖ).inverse).obj P),
      ∀ (n : ℕ) (i : ℤ) (U : T.ProEtᵒᵖ)
        (b : ((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n)).obj.obj U)
        (x : (P.X i).val.obj U),
        (((r.hom.f i).app (op n)).val.app U)
            (reductionTensorSection T
              (completedReductionProjection T (pbcIntegralDatum l E) n)
              ((pbcRestrict e.hom).obj (P.X i)) U b x) =
          unrestrictedIntegralTensorSection l E T n (P.X i) U
            ((IntegralCoefficientPresentation.level l E T q n).hom.hom.app U b) x := by sorry

end WeilConjectures.PointQuotientTower
