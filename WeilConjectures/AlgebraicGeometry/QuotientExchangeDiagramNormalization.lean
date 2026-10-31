/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectQuotientExchangePresentation

/-! # Normalized exchange on the quotient diagram

Source: Stacks Project, Tags 03D7, 06YY, 07A6, 0D6E, 0B56 and 0940.
(blueprint: lem-pur-quotient-exchange-diagram-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace CategoryTheory.AdicSites.PerfectQuotientExchange

variable {Y X : Site.{u}} (f : Morphism Y X) (A : Type u) [CommRing A] (I : Ideal A)

/-- The quotient-diagram adjunction and its scalar and evaluation mate equations.
This construction is independent of perfectness of the coefficient quotients.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 0D6E and equation 0B56;
Modules on Sites, Tags 03D7 and 06YY; the diagram construction of Tag 0940
(blueprint: lem-pur-quotient-exchange-diagram-normalization).

Proof:
1. Use the sequence-site realization for the actual quotient coefficient systems. Lift
inverse image levelwise using the given algebraic inverse image and its natural constant
ring identifications. Restriction of scalars along the quotient transitions makes these
functors a functor on semilinear systems. Assemble the component adjunctions; their Hom
equations are compatible with transitions. Transport along the sequence equivalences.
2. The strict diagonal presentation supplies the diagonal, scalar extension and exact
restriction. On local pure tensors, evaluation of extension is extension at that level,
and scalar restriction leaves sections unchanged. Localize these comparisons on flat-term
K-flat representatives. Their scalar-extension counits give the full cochain equations
of PresentationNormalized. Use evaluation-adjunction normalization for pushEvaluationD;
its derived-unit square is exactly the final clause of PresentationNormalized.
3. The diagram restriction/pushforward theorem gives the common-composite derived
isomorphism d. Restriction-counit compatibility identifies its counit transpose with
restrictionMate. Coefficient pullback-extension coherence identifies the transpose of
restricted exchange followed by d with the strict counit tensor identity. The fixed
constant-tower comparison has this same counit normalization. Injectivity of the tower
adjunction therefore identifies this morphism with strictExchange, before evaluation.
4. The evaluation-adjunction theorem preserves the derived counit and transposes. Apply
its transpose equation to exchange. The normalized scalar-extension comparison becomes
the fixed finitePullIso, so this is finiteProjection. Its evaluation/restriction square
then gives the displayed equality between restriction of finiteExchange and evaluation
of strictExchange, including all endpoint comparisons. Every coefficient transition
is the original quotient restriction. No perfectness or derived-evaluation faithfulness
is used, including for zero quotients or an empty site. -/
theorem quotientExchangeDiagramNormalization [IsNoetherianRing A] :
    ∃ (p : Presentation f A I)
      (d : p.push.rightDerivedFunctor ⋙ p.atY.restrictionD ≅
        p.atX.restrictionD ⋙ f.towerPush A),
      PresentationNormalized f A I p ∧
      d.hom = restrictionMate p ∧
      (∀ F : X.derived A,
        p.atY.restrictionD.map ((exchange p).app F) ≫
            d.hom.app (p.atX.reductionD.obj F) = (strictExchange p).app F) ∧
      (∀ (F : X.derived A) (n : ℕ),
        (finiteExchange p n).app F = f.finiteProjection A I n F) ∧
      (∀ (F : X.derived A) (n : ℕ),
        (Y.evaluate A n).map ((strictExchange p).app F) ≫
            (Y.evaluate A n).map
              ((f.towerPush A).map (p.reductionX.tower.hom.app F)) ≫
            (f.evaluatePushIso A n).hom.app ((X.reduction A I).obj F) ≫
            (f.push A).map ((X.finiteEvaluationIso A I n).hom.app F) ≫
            (f.finiteRestrictionPushIso A I n).hom.app ((X.finiteReduction A I n).obj F) =
          (Y.evaluate A n).map (p.reductionY.tower.hom.app ((f.push A).obj F)) ≫
            (Y.finiteEvaluationIso A I n).hom.app ((f.push A).obj F) ≫
            (Y.finiteRestriction A I n).map ((finiteExchange p n).app F)) := by
  sorry

end CategoryTheory.AdicSites.PerfectQuotientExchange
