/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefFinitePairingEvaluationData

/-! # Finite comparison witnesses for the projection word

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

/-- Finite comparison data for an already normalized system model, without an equation
for its projection-evaluation pairing. This is only the simultaneous construction of
comparisons: it does not assert compatibility of the composite Model.beta.

Source: blueprint latest, prop-coef-integral-dualizing.proof.md, paragraph 2;
Stacks 07A6 (lemma-adjoint), 0B56 (equation-projection-formula-map), 08J9 and 0941
(blueprint: lem-sf-coef-finite-evaluation-existence).

Proof: specialize the ordinary-derived semilinear system calculus to the quotient
coefficient tower on X, Y and the compactification. At each level use the prescribed
finite closed tensor, its signed total-complex localization, and the finite ordinary
sections, proper-image and scalar adjunctions. The universal localization comparisons
supply the point and site tensor evaluations, with their ordinary components fixed on
pure sections. Evaluate the ordinary sections and scalar squares and derive their
comparisons using the universal right-derived units. Conjugate their adjunctions to
obtain gx, gy and r and the displayed unit and counit equations. The same geometric
comparison gives properUnit and properCounit and the strong tensor squares.
Composition of the actual inverse-image functors gives composition and
pullbackComposition, preserving the derived units. The support-open-tensor model
identifies gamma with the evaluation of its sheafified pure-tensor chain map. Finally
s.reductionModel identifies s.reduced K with derived scalar extension of the constant
K system. Associativity of scalar extension makes it cartesian. Cartesian-first-input
Hom evaluation therefore supplies hom for arbitrary N; its adjoint transpose gives
hom_normalization. Assemble these comparisons into FiniteEvaluation. All choices are
of witnesses normalized by these universal properties; no arbitrary object is defined
from this existence assertion. No evaluation is assumed to preserve K-injectivity. -/
theorem finiteEvaluation_exists
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (_hl : IsUnit (l : k)) (c : Compactification a)
    (m : Model l E c) (s : ScalarSpecialization l E m) (n : ℕ) :
    Nonempty (FiniteEvaluation l E m s n) := by sorry

end WeilConjectures.CoefProjectionEvaluation
