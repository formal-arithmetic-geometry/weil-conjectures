/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCoefficientSystem

/-! # Finite native realization cocones

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

variable (C : CoefficientSystem l X)
variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]

/-- A finite-field realization cocone. Every comparison is specified before descent;
no functor on the pair category, Hom descent, or essential-image assertion is assumed.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-finite-cocone). -/
structure FiniteCoconeData where
  Φ : ∀ E : Index l (PadicAlgCl l),
    GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E ⥤
      DerivedCategory (ProEtale.AdicSheaf l X)
  [additive : ∀ E, (Φ E).Additive]
  [shift : ∀ E, (Φ E).CommShift ℤ]
  triangulated : ∀ E, (Φ E).IsTriangulated
  ι : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙ Φ L ≅ Φ E
  coherence : ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (h' : L ≤ M)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E),
    (Φ M).map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).assoc
          h h').hom.app K) ≫ (ι (h.trans h')).hom.app K =
      (ι h').hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj K) ≫
          (ι h).hom.app K
  [transitionShift : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
    NatTrans.CommShift (ι h).hom ℤ]
  integral : ∀ E : Index l (PadicAlgCl l),
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      Φ E ⋙ (sections l X).mapDerivedCategory ≅
      ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
        pbcDerivedExtend.{u} ((C.coefficient E).integralMap l X)

/-- The finite-stage completion-map equation, before pair-category descent.
Source: Bhatt--Scholze, Proposition 6.8.14, Remark 6.8.15
(blueprint: lem-sf-locally-finite-adic-finite-cocone). -/
@[irreducible] def FiniteCoconeData.normalized (A : FiniteCoconeData l X C) : Prop :=
  ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    HEq
      ((sections l X).mapDerivedCategory.map
        ((A.ι h).inv.app ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)))
      ((A.integral E).hom.app K ≫
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((C.coefficient L).integralMap l X) ((C.coefficient E).integralMap l X)
          (C.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((C.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj) ≫
        (A.integral L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
            E L h).obj K))


/-- The finite realization data with its completion-map equation.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-finite-cocone). -/
structure FiniteCocone extends FiniteCoconeData l X C where
  normalization : toFiniteCoconeData.normalized l X C

/-- The finite-field tensor realizations form a normalized coherent cocone.

Source: Bhatt--Scholze, Proposition 6.8.11(3), Proposition 6.8.14(2) and Remark 6.8.15;
native realization proof steps 3--4
(blueprint: lem-sf-locally-finite-adic-finite-cocone).

Proof in words: identify the strict-tower raw rational category at E with the completed
integral raw rationalization through the integral identity equivalence. Compose its
continuous rational derived realization with extension from E-valued functions to native
functions, and the inverse of the native section-module equivalence. This defines Φ_E.
All these functors are additive and triangulated. On integral representatives their
comparison is the balanced derived tensor associator, which flattens b tensor (e tensor k)
to be tensor k; its inverse inserts one. The same maps send inverse uniformizer powers
to their inverses, so the integral comparison is natural on all fractions. For E ≤ L,
compose the inverse-completion scalar comparison between the two raw rationalizations
with the finite realization scalar comparison and tensor transitivity to get ι. Both
routes for E ≤ L ≤ M flatten three scalar factors to their product. The scalar coherence
and completion-unit equations therefore give coherence, including repeated fields and
ramification. All constituent maps commute with shifts. For an integral K the inverse
of ι is the completion-chain comparison followed by the same balanced associator;
the normalization of the raw scalar comparison gives exactly the displayed equation.
Only finite fields occur here: no quotient of common-stage arrows is taken.
-/
theorem finiteCocone_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (C : CoefficientSystem l X) :
    letI := C.commutative
    letI := C.sectionsAdditive
    letI := C.sectionsLimits
    letI := C.sectionsColimits
    Nonempty (FiniteCocone l X C) := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
