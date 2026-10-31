/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonData

/-! # Normalized rational smooth-purity comparison: an intermediate step -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.RationalScalarComparisonIdentification
open AdicPurityScalarNaturality
attribute [local irreducible] O G H T Q alpha unit LocalizesComparison
  PuritySquares UnitEquation CompositionEquation SourceLocalizationNormalization
  AdicPurityScalarNaturality.source AdicPurityScalarNaturality.target

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (I : Data D C f d S)

/-- Ordinary completed scalar extension localizes to the specified rational scalar
functor, with its completion map, unit, associator, and integer-shift normalization.
Source: smooth purity coefficient passage, parent proof Step 2 and Step 9.
(blueprint: lem-pur-rational-scalar-localization).
Proof: on complete integral objects use the finite-free completed scalar comparison
chi. Restrict it to the finite-Tor domain and apply Q. The rational scalar functor's
object and pure-tensor map clauses identify the resulting functor with T. Naturality
of chi makes these components a natural isomorphism; its components are precisely
Q(scalarBridge). CompletedScalarChainShift identifies the shift comparison with the
one fixed by scalarShift_existsUnique, first at degree one and then at every integer.
Exactness follows from integral exactness and the image triangulation of localization.
The identity normalization of chi gives the displayed scalar-unit equation.
ScalarCompletionAssociator identifies both three-field paths with the ordinary
balanced tensor associator. Applying Q and functoriality gives the displayed
composition equation, retaining the published alpha and unit. -/
theorem rationalPurityScalarLocalization :
  ∃ (scalarLocalization : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (side : Bool),
      scalar D C I.scalarClosed E F h side ⋙
        Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side) ≅
      Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side) ⋙
        T D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side)),
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (side : Bool)
      (K : Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)),
      HEq ((scalarLocalization E F h side).hom.app K)
      ((Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side)).map
        (scalarBridge D C f S I.scalarClosed E F h side K).hom)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (side : Bool),
      ShiftCompatibility
      (scalar D C I.scalarClosed E F h side ⋙
        Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side))
      (Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side) ⋙
        T D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side))
      (composeShift _ _ (scalarShift D C I.scalarClosed E F h side) (qSideShift D C f S F side))
      (composeShift _ _ (qSideShift D C f S E side)
        (tShift D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side)))
      (scalarLocalization E F h side)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (side : Bool),
      (fun [_cs : (T D C E F h
      (ConstructibleExceptionalCoefficients.endpoint X Y side)).CommShift ℤ] ↦
        (T D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side)).IsTriangulated)
      (_cs := tShift D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side))) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C) (side : Bool)
      (K : Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)),
      (Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).map
        ((scalarUnit D C I.scalarClosed E side).hom.app K) =
      (scalarLocalization E E le_rfl side).hom.app K ≫
        (unit D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).hom.app
          ((Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).obj K)) ∧
  (∀ (E F L : AdicPurityScalarNaturality.Field D C)
      (h : E ≤ F) (k : F ≤ L)
      (side : Bool) (K : Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)),
      (Q D C L (ConstructibleExceptionalCoefficients.endpoint X Y side)).map
        ((associator D C I.scalarClosed E F L h k side).hom.app K) ≫
        (scalarLocalization E L (h.trans k) side).hom.app K =
      (scalarLocalization F L k side).hom.app ((scalar D C I.scalarClosed E F h side).obj K) ≫
        (T D C F L k (ConstructibleExceptionalCoefficients.endpoint X Y side)).map
          ((scalarLocalization E F h side).hom.app K) ≫
        (alpha D C E F L h k (ConstructibleExceptionalCoefficients.endpoint X Y side)).hom.app
          ((Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).obj K)) := by sorry

end WeilConjectures.RationalScalarComparisonIdentification
