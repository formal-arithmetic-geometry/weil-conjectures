module

public import Sheaf.Paper.RationalScalarComparisonData
import Sheaf.Paper.RationalExceptionalFinalEquations
import Sheaf.Paper.RationalPuritySourceLocalization
import Sheaf.Paper.RationalPurityScalarLocalization
import Sheaf.Paper.RationalPurityComparisonDescent
import Sheaf.Paper.RationalPurityCoherenceDescent

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u uI uR vI vR
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

/-- The complete localized comparison data and all purity, coefficient and shift equations.
Source: smooth purity transport Steps 2--4, coefficient passage
(blueprint: lem-pur-rational-scalar-comparison-identification). -/
def Result : Prop :=
  ∃ (hShift : ∀ (E : AdicPurityScalarNaturality.Field D C),
      (H D C f d E).CommShift ℤ),
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      (fun [_cs : (H D C f d E).CommShift ℤ] ↦ (H D C f d E).IsTriangulated)
      (_cs := hShift E)) ∧
  ∃ (hLocalization : ∀ (E : AdicPurityScalarNaturality.Field D C),
      source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E),
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      SourceLocalizationNormalization D C f d E (hLocalization E)) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      ShiftCompatibility (source D C f d E ⋙ Q D C E X) (Q D C E Y ⋙ H D C f d E)
      (composeShift _ _ (sourceShift D C f d E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (hShift E)) (hLocalization E)) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      ShiftCompatibility (target D C f S E ⋙ Q D C E X)
      (Q D C E Y ⋙ G D C f S E)
      (composeShift _ _ (targetShift D C f S E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (gShift D C f S E)) (gLocalization D C f S E)) ∧
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
          ((Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).obj K)) ∧
  ∃ (eta : ∀ (E : AdicPurityScalarNaturality.Field D C),
      H D C f d E ≅ G D C f S E),
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      ShiftCompatibility (H D C f d E) (G D C f S E)
      (hShift E) (gShift D C f S E) (eta E)) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C) (K : Cat D C E Y),
      (hLocalization E).hom.app K ≫ (eta E).hom.app ((Q D C E Y).obj K) =
      (Q D C E X).map ((I.gamma E).hom.app K) ≫
        (gLocalization D C f S E).hom.app K) ∧
  ∃ (a : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      H D C f d E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ H D C f d F),
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      ShiftCompatibility (H D C f d E ⋙ T D C E F h X)
      (T D C E F h Y ⋙ H D C f d F)
      (composeShift _ _ (hShift E) (tShift D C E F h X))
      (composeShift _ _ (tShift D C E F h Y) (hShift F)) (a E F h)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      ShiftCompatibility (G D C f S E ⋙ T D C E F h X)
      (T D C E F h Y ⋙ G D C f S F)
      (composeShift _ _ (gShift D C f S E) (tShift D C E F h X))
      (composeShift _ _ (tShift D C E F h Y) (gShift D C f S F)) (b D C f S E F h)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (K : RCat D C E Y),
      HEq ((a E F h).app K) (RationalSmoothPurityCanonical.sourceScalar C.l E.val F.val
      (IntermediateField.inclusion h) f d K)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      LocalizesComparison (hLocalization E) (hLocalization F)
      (scalarLocalization E F h true) (scalarLocalization E F h false)
      (I.a E F h) (a E F h)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      LocalizesComparison (gLocalization D C f S E) (gLocalization D C f S F)
      (scalarLocalization E F h true) (scalarLocalization E F h false)
      (integralB D C f d S I E F h) (b D C f S E F h)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (K : RCat D C E Y),
      (b D C f S E F h).hom.app K =
      coefficientTranspose D C f S E F h K) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      PuritySquares (eta E) (eta F) (a E F h) (b D C f S E F h)) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      UnitEquation (a E E le_rfl) (unit D C E X) (unit D C E Y)) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      UnitEquation (b D C f S E E le_rfl) (unit D C E X) (unit D C E Y)) ∧
  (∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
      CompositionEquation (a E F h) (a F L k) (a E L (h.trans k))
      (alpha D C E F L h k X) (alpha D C E F L h k Y)) ∧
  (∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
      CompositionEquation (b D C f S E F h) (b D C f S F L k)
      (b D C f S E L (h.trans k)) (alpha D C E F L h k X) (alpha D C E F L h k Y))


/-- Source: current blueprint smooth purity transport, coefficient passage.
(blueprint: lem-pur-rational-scalar-comparison-identification).
Proof: use the quotient completion map and its associator and shift normalization.
Localize the supplied exact linear functors and maps. Pin the source identification
on every good representative of the integral pullback: identify the termwise twist
with tensor by the degree-zero integral Tate line, apply the sheaf tensor symmetry,
invert the single-summand totalization and first-factor shift comparison, and apply
the strict quotient tensor augmentation and completed-tensor representative
comparison. The single line is flat and remains good under every integer shift.
Use the object clauses of rationalDerivedPullback_existsUnique and
rationalDerivedTensor_existsUnique and the localization shift comparison to obtain
the specified rational endpoint. Naturality and good resolutions make these
components independent of the representative. The eta localization equation then
transports precisely Q(I.gamma), rather than a simultaneous automorphism of the
source and purity map. Identify the exceptional functor by its fixed integral
comparison. Localize the
adjunction Hom bijections, hence its counits. The localized exceptional comparison
has exactly the counit transpose defining the specified rational comparison, so
injectivity of the Hom bijection identifies them. The source comparison is the
localized pullback, tensor, twist and shift comparison. Extend naturality from
integral arrows to scalar multiples and sums. Apply localization to the purity
square, and cancel inverse pairs for its inverse equation. Finally localize all
unit, associator and shift equations, retaining their specified normalizations. -/
theorem rationalScalarComparisonIdentification : Result D C f d S I := by
  obtain ⟨hShift, hExact, hLocalization, hNorm, hLocShift⟩ :=
    rationalPuritySourceLocalization D C f d S I
  obtain ⟨scalarLocalization, hScalarNorm, hScalarShift, hScalarExact, hUnit, hComp⟩ :=
    rationalPurityScalarLocalization D C f d S I
  obtain ⟨eta, hEtaShift, hEta, a, hAShift, hBShift, hCanonical, hA, hB⟩ :=
    rationalPurityComparisonDescent D C f d S I hShift hLocalization hNorm
      hLocShift scalarLocalization hScalarNorm
  obtain ⟨hSquare, hAUnit, hAComp⟩ :=
    rationalPurityCoherenceDescent D C f d S I hLocalization scalarLocalization
      eta a hEta hA hB hUnit hComp
  obtain ⟨hFinalShift, hFinalB, hFinalUnit, hFinalComp⟩ :=
    rationalExceptionalFinalEquations D C f S
  refine ⟨hShift, hExact, hLocalization, hNorm, hLocShift, ?_, scalarLocalization,
    hScalarNorm, hScalarShift, hScalarExact, hUnit, hComp, eta, hEtaShift, hEta,
    a, hAShift, hBShift, hCanonical, hA, hB, ?_, ?_, hAUnit, ?_, hAComp, ?_⟩
  · exact hFinalShift
  · exact hFinalB
  · intro E F h
    unfold PuritySquares
    refine ⟨hSquare E F h, ?_⟩
    intro K
    have he :
        (T D C E F h X).mapIso ((eta E).app K) ≪≫ (b D C f S E F h).app K =
          (a E F h).app K ≪≫ (eta F).app ((T D C E F h Y).obj K) :=
      Iso.ext (hSquare E F h K)
    exact congrArg Iso.inv he
  · exact hFinalUnit
  · exact hFinalComp

end WeilConjectures.RationalScalarComparisonIdentification
