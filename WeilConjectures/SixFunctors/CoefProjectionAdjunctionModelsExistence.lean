/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefProjectionEvaluationData

/-! # Normalized coefficient tensor adjunction witnesses

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 07A6, 08J9, 0D6D and 0B56.
(blueprint: lem-sf-coef-projection-adjunction-models-existence).
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

/-- Normalized ordinary and derived tensor adjunctions for quotient point sections,
native system direct image, and point scalar restriction, with prescribed lax maps.
The tensor models are inputs; neither open extension nor any Hom comparison is asserted.

Source: Stacks 03D7, 07A4, 07A6 and 0B56; projection-evaluation steps 1 and 6.
(blueprint: lem-sf-coef-projection-adjunction-models-existence).

Proof: construct the three ordinary module adjunctions by inverse image followed
by extension of scalars. Quotient sections are evaluation at (n,W), proper image
is evaluation at the base-changed object, and point restriction forgets only the
quotient scalar action. Their ordinary lax tensors send a pair of local sections
to its actual sheafified pure tensor; the quotient actions make the point map
balanced. The adjoint transpose of the tensor of the ordinary units is the
canonical pullback tensor isomorphism. Resolve sources K-flatly and targets
K-injectively. The resolving adjunction gives the derived left adjoint and its
universal counit, with the transpose equation relative to rightUnit, or to the
exact restriction comparison. The totalized ordinary tensor isomorphism and the
universal tensor counits induce TensorAdjunction.comparison. Check its displayed
representative identity on resolving representatives, then use naturality and
the localization universal property to extend it to all complexes. Apply this
construction to sections on X and Y, direct image along f and point restriction.
No geometric property of f, finite-Tor condition or invertible projection mate
is used. The identity morphism and zero complexes give the unit and zero cases. -/
theorem coefficientProjectionAdjunctionModels_exists
    (X Y Z : Scheme.{u}) (f : Z ⟶ Y)
    (point : PointTensor l E)
    (x : SystemTensor l E X) (y : SystemTensor l E Y) (z : SystemTensor l E Z) :
    ∃
      (xLax : SectionsTensor l E X)
      (yLax : SectionsTensor l E Y)
      (pLax : PushTensor l E f)
      (rLax : RestrictionTensor l E)
      (gx : AdjointLocalization (coefHomQuotientSections l E X)
    (coefHomQuotientDerivedSections l E X) (rightUnit (coefHomQuotientSections l E X)))
      (gy : AdjointLocalization (coefHomQuotientSections l E Y)
    (coefHomQuotientDerivedSections l E Y) (rightUnit (coefHomQuotientSections l E Y)))
      (p : AdjointLocalization
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f)
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f)
    (rightUnit (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f)))
      (r : AdjointLocalization (coefHomPointRestriction l E)
    (coefHomPointDerivedRestriction l E) (restrictionUnit l E)),
      Nonempty (TensorAdjunction point.qTensor x.data.systemClosed.tensor
    point.quotientLocalization x.localization
    (coefHomQuotientSections l E X) (coefHomQuotientDerivedSections l E X)
    (rightUnit (coefHomQuotientSections l E X)) xLax.map gx) ∧
      Nonempty (TensorAdjunction point.qTensor y.data.systemClosed.tensor
    point.quotientLocalization y.localization
    (coefHomQuotientSections l E Y) (coefHomQuotientDerivedSections l E Y)
    (rightUnit (coefHomQuotientSections l E Y)) yLax.map gy) ∧
      Nonempty (@TensorAdjunction
    (coefficientSequenceModules.{u, u} l E Y) _ _ _ _ _ _
    (coefficientSequenceModules.{u, u} l E Z) _ _ _ _ _ _
    y.data.systemClosed.tensor z.data.systemClosed.tensor y.localization z.localization
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f) (systemPushAdditive l E f)
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f)
    (rightUnit (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f)) pLax.map p) ∧
      Nonempty (TensorAdjunction point.rTensor point.qTensor
    point.integralLocalization point.quotientLocalization
    (coefHomPointRestriction l E) (coefHomPointDerivedRestriction l E)
    (restrictionUnit l E) rLax.map r) := by sorry

end WeilConjectures.CoefProjectionEvaluation
