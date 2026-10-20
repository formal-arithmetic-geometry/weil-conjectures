/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.WfTensorCompletionFrobenius
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
public import Sheaf.SixFunctors.OpenFactorTensorModel
public import Sheaf.Paper.ProjectionCoefficientTensorTotal

/-! # The representative-normalized tensor comparison for projection

Source: main-20261015, projection-formula proof step 13
(blueprint: def-sf-projection-tensor-coefficient-comparison).
The ordinary comparison is fixed on homogeneous local pure tensors. Derived
descent and the specified quotient-completion unit then fix its integral and
rational constructible restrictions.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ProjectionTensorCoefficient

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

/-- Coefficient restriction preserves the precise resolving class.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: an exact equivalence preserves acyclicity and tensor flatness. The local
pure-tensor isomorphism identifies tensoring a transported complex with
transporting its tensor against the inverse-transported complex. Thus K-flatness
and termwise flatness are preserved without a boundedness restriction. -/
theorem good (P : (proEtaleFlatRepresentatives X
      (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory) :
    proEtaleFlatRepresentatives X (pbcAdicCompletion X (pbcIntegralDatum l E))
      ((complexTransport l E X).obj P.obj) := by
  sorry

/-- Ordinary coefficient transport is fixed by the signed-total representative square.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: compose the specified representative comparisons with total, and with the
exact transport factorization. The good theorem supplies the target resolving
objects. Double K-flat localization extends this square uniquely to a natural
isomorphism. Its inverse is obtained from the inverse total comparison. -/
theorem ordinary_existsUnique
    (T : ProEtaleTensorModel X (completedIntegralCommRingSheafUnrestricted l E X)) :
    ∃! e : T.tensor ⋙ integralDetailedTransport X l E ≅
        ((integralDetailedTransport X l E).prod (integralDetailedTransport X l E)) ⋙
          wfOrdinaryDerivedTensor X (pbcIntegralDatum l E),
      ∀ P Q : (proEtaleFlatRepresentatives X
        (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory,
        (integralDetailedTransport X l E).map (T.representative.hom.app (P, Q)) ≫
          e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (wfOrdinaryDerivedTensor X (pbcIntegralDatum l E)).map
            (Prod.mkHom
              ((fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app P.obj)
              ((fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (wfTensorModel X (pbcIntegralDatum l E)).representative.inv.app
            (⟨(complexTransport l E X).obj P.obj, good l E X P⟩,
              ⟨(complexTransport l E X).obj Q.obj, good l E X Q⟩) =
        (fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app
            ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map ((totalIso l E X P.obj Q.obj).hom) := by
  sorry

/-- The representative-normalized ordinary derived comparison.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def ordinaryComparison
    (T : ProEtaleTensorModel X (completedIntegralCommRingSheafUnrestricted l E X)) :
    T.tensor ⋙ integralDetailedTransport X l E ≅
      ((integralDetailedTransport X l E).prod (integralDetailedTransport X l E)) ⋙
        wfOrdinaryDerivedTensor X (pbcIntegralDatum l E) :=
  (ordinary_existsUnique l E X T).exists.choose

/-- Every normalized tensor-completion presentation has invertible comparison
on constructible pairs. This is the actual completion unit, not an assumption.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: the presentation's representative square and its two chain coordinates
identify chi with the quotient-map completion unit. Constructible tensor
completion makes that unit invertible, and tensor descent identifies its
ordinary tensor presentation with the presentation used there. -/
theorem completion_isIso (t : OpenFactorCoherence.Tensor l E X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [∀ x : X, Invertible (l : X.residueField x)]
    (M N : sfIntegralConstructibleCategory l E X) :
    IsIso ((t.chi l E).app (M.obj, N.obj)) := by
  sorry

end WeilConjectures.ProjectionTensorCoefficient

namespace WeilConjectures.CompactSupportCoefficientTensor
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
  (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
  (F : FdCoefficientComparisonSystem.{u} C.l C.Qbar)
  (W : FdFrobeniusComparison C.l C.Qbar D C.different F T₀)

/-- The recorded integral coefficient equivalence at this field and scheme.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def integral :=
  letI := W.noetherian
  letI := W.dimension
  letI := W.invertible
  ((F.coefficients (D.geometricFiber T₀).left).stage E₀).integral.functor

/-- The recorded rational coefficient equivalence at this field and scheme.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def rational :=
  letI := W.noetherian
  letI := W.dimension
  letI := W.invertible
  ((F.coefficients (D.geometricFiber T₀).left).stage E₀).rational.functor

/-- Integral completed tensor in the framework convention.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def integralTensor :=
  letI := sfWeilPrimeInvertible D C.l C.different T₀
  constructibleIntegralTensor C.l (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left

/-- Rational tensor in the framework convention.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def rationalTensor :=
  letI := sfWeilPrimeInvertible D C.l C.different T₀
  rationalDerivedTensor C.l (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left

/-- The coefficient tensor map on integral objects: inverse quotient-completion
unit, followed by the representative-normalized ordinary coefficient comparison.
Its underlying map is prescribed, not merely asserted to be invertible.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def integralArrow
    (t : OpenFactorCoherence.Tensor C.l (pbcFiniteField C.l C.Qbar E₀)
      (D.geometricFiber T₀).left)
    (M N : sfIntegralConstructibleCategory C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left) :=
  letI := sfWeilPrimeInvertible D C.l C.different T₀
  (integralDetailedTransport (D.geometricFiber T₀).left C.l
    (pbcFiniteField C.l C.Qbar E₀)).map
      (@asIso _ _ _ _
        ((t.chi C.l (pbcFiniteField C.l C.Qbar E₀)).app (M.obj, N.obj))
        (ProjectionTensorCoefficient.completion_isIso C.l (pbcFiniteField C.l C.Qbar E₀)
          (D.geometricFiber T₀).left t M N)).inv ≫
    (ProjectionTensorCoefficient.ordinaryComparison C.l (pbcFiniteField C.l C.Qbar E₀)
      (D.geometricFiber T₀).left t.ordinary).hom.app (M.obj, N.obj)

/-- The full integral lift of the specified underlying coefficient tensor arrow.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: integral_identity fixes the underlying objects and maps of the coefficient
equivalence. Thus integralArrow has these endpoints after those equalities.
Constructible fullness lifts it and its inverse. Each normalized tensor model
gives the same arrow: the representative comparison cancels its own completion
unit, while the chain normalization fixes both Roos coordinates. Such a model
exists by the tensor-completion theorem and K-flat descent, so the universal
normalization is nonvacuous and faithfulness makes its lift unique. -/
theorem integral_existsUnique
    (M N : sfIntegralConstructibleCategory C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left) :
    ∃! e : (integral D C T₀ E₀ F W).obj ((integralTensor D C T₀ E₀).obj (M, N)) ≅
        (WfTensorCompletion.ordinary D C T₀ E₀).obj
          ((integral D C T₀ E₀ F W).obj M, (integral D C T₀ E₀ F W).obj N),
      ∀ t : OpenFactorCoherence.Tensor C.l (pbcFiniteField C.l C.Qbar E₀)
        (D.geometricFiber T₀).left,
        HEq e.hom.hom (integralArrow D C T₀ E₀ t M N) := by
  sorry

/-- The integral comparison selected only from its uniquely prescribed arrow.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def integralComparison
    (M N : sfIntegralConstructibleCategory C.l
      (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left) :=
  (integral_existsUnique D C T₀ E₀ F W M N).exists.choose

/-- Rational tensor compatibility retains the canonical integral comparison on
every unchanged integral representative. Bilinearity fixes every denominator.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: localize integralComparison and its inverse. The integral_identity,
objects and tensors fields of the coefficient comparison identify the localized
endpoints and maps. The normalization of R.ordinary does the same for the tensor.
Naturality on integral maps extends by bilinearity to all localized maps.
All rational objects are unchanged integral representatives, giving uniqueness. -/
theorem rational_existsUnique
    (R : WfTensorCompletion.RationalComparison D C T₀ E₀)
    (hR : R.Normalized D C T₀ E₀) :
    ∃! e : rationalTensor D C T₀ E₀ ⋙ rational D C T₀ E₀ F W ≅
        ((rational D C T₀ E₀ F W).prod (rational D C T₀ E₀ F W)) ⋙ R.ordinary,
      ∀ M N : sfIntegralConstructibleCategory C.l
        (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left,
        HEq (e.hom.app
          ((sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
            (D.geometricFiber T₀).left).obj M,
            (sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
              (D.geometricFiber T₀).left).obj N))
          ((pbcStageLocalization C.l C.Qbar (D.geometricFiber T₀).left E₀).map
            (integralComparison D C T₀ E₀ F W M N).hom) := by
  sorry

/-- The rational coefficient tensor comparison with its integral normalization.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison). -/
def comparison
    (R : WfTensorCompletion.RationalComparison D C T₀ E₀)
    (hR : R.Normalized D C T₀ E₀) :
    rationalTensor D C T₀ E₀ ⋙ rational D C T₀ E₀ F W ≅
      ((rational D C T₀ E₀ F W).prod (rational D C T₀ E₀ F W)) ⋙ R.ordinary :=
  (rational_existsUnique D C T₀ E₀ F W R hR).exists.choose

end WeilConjectures.CompactSupportCoefficientTensor
