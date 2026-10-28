/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefFinitePairingEvaluationData

/-! # Evaluation of the untransported projection word

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2; Stacks 07A6, 0B56.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation of the untransported system projection word, on a scalar-reduced first
input. The full-system scalar-Hom isomorphism and ScalarSpecialization.transported do
not occur in this equation.

Source: blueprint latest, prop-coef-integral-dualizing.proof.md, paragraph 2;
Stacks 07A6 (lemma-adjoint) and 0B56 (equation-projection-formula-map)
(blueprint: lem-sf-coef-finite-projection-word-evaluation).

Proof: expand Model.beta into balance, signed symmetry and q, then expand q into the
sections projection, Pi and v. Evaluate each composite in that order. For balance,
e.rUnit, e.rCounit and e.rTensor identify the scalar projection mate and its counit
with finite scalar balancing. e.symmetry identifies the signed point interchange.
For the sections projection, e.gyUnit, e.gyCounit and e.gyTensor identify its adjoint
transpose with the finite one. For Pi use e.properUnit, e.properCounit and
e.properTensor; its transpose is precisely counit tensor identity after the strong
tensor comparison. e.gamma identifies the open factor with the finite sheafified
chain map; e.pullbackComposition identifies the compactification pullback composite.
For v use e.composition and e.gxCounit, then e.hom_normalization: the closed evaluation
is carried to finite evaluation because the Hom comparison is its tensor-Hom
transpose. This applies to arbitrary N since only the first input s.reduced K is
cartesian. Use the reduction-unit isomorphism s.reductionEvaluation to replace its
finite evaluation by the prescribed K_n. Naturality in the first Hom input and in
compact support supplies the displayed inverse Hom reduction and forward support
reduction. The support comparison is the separately derived proper comparison after
exact open extension, followed by sections evaluation. Cancel consecutive comparison
inverses using naturality and associativity. The remaining composite is FiniteModel.beta,
with precisely the tensor, scalar balancing, symmetry and evaluation order displayed
below. The argument evaluates an existing composite; it does not reconstruct a
system morphism from its finite components. -/
theorem finiteProjectionWord_evaluation
    {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
    {m : Model l E c} {s : ScalarSpecialization l E m} {n : ℕ}
    (e : FiniteEvaluation l E m s n)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (N : coefficientSequenceDerived.{u, u} l E X) :
    let homComparison :=
      (restrictionEvaluation l E n).app (Model.h (s.reduced K) N) ≪≫
        (finiteDerivedRestriction l E n).mapIso
          (e.sectionsX.derived.app (Model.hom (s.reduced K) N) ≪≫
            (finiteDerivedSections l E X n).mapIso (e.hom K N) ≪≫
            (finiteDerivedSections l E X n).mapIso
              ((coefficientFiniteInternalHom l E X n).mapIso
                (Iso.prod ((s.reductionEvaluation n).app K).symm.op (Iso.refl _))))
    let supportComparison := fun U : coefficientSequenceDerived.{u, u} l E X ↦
      (restrictionEvaluation l E n).app (m.b U) ≪≫
        (finiteDerivedRestriction l E n).mapIso
          (e.sectionsY.derived.app (m.support.obj U) ≪≫
            (finiteDerivedSections l E Y n).mapIso ((supportEvaluation l E c n).app U))
    let reducedSupport := supportComparison (s.reduced K) ≪≫
      (finiteDerivedRestriction l E n).mapIso
        ((finiteDerivedSections l E Y n).mapIso
          ((finiteSupport l E c n).mapIso ((s.reductionEvaluation n).app K)))
    (coefHomPointEvaluation l E n).map (m.beta (s.reduced K) N) ≫
        (supportComparison N).hom =
      e.integral.derived.hom.app
          ((coefHomPointDerivedRestriction l E).obj (Model.h (s.reduced K) N),
            s.supportTower K) ≫
        e.finite.integralTensor.map
          (Prod.mkHom homComparison.hom reducedSupport.hom) ≫
        e.finite.beta ((coefficientFiniteDerivedExtension l E X n).obj K)
          ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by sorry

end WeilConjectures.CoefProjectionEvaluation
