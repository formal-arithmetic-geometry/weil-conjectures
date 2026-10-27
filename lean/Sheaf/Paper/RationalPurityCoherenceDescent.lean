/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.RationalScalarComparisonData

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

/-- Forward purity and source coefficient coherence descend through the fixed
localization isomorphisms. No inverse-square equation is assumed.
Source: current blueprint coefficient change, rational case (2) and field extensions
(3); parent proof Steps 7--9.
(blueprint: lem-pur-rational-purity-coherence-descent).
Proof: integral_residue_tor identifies integral constructibility with
uniform finite-Tor constructibility, so every raw rational object is Q(K) for a
finite-Tor K. For the forward square precompose with T(hLocalization.hom).
Use hEta at E, the scalarLocalization naturality square for I.gamma, and hB.
Functoriality of Q carries the integral purity square I.coherence to an equality.
Use hEta at F and eta's naturality for scalarLocalization to obtain hA followed by
eta. Cancel the invertible precomposition. For the unit equation precompose with
the scalar localization and T(hLocalization.hom), use hA, hUnit, and naturality
of hLocalization for the integral unit. Apply Q to the integral source unit
identity in I.coherence; scalar unit naturality gives the desired equation after
cancellation. For composition precompose with the two scalar localizations and
the twice-extended hLocalization.hom. Naturality moves hLocalization through the
rational associator; hComp replaces it by Q of the integral associator. Use hA
at each extension and naturality for the middle scalar localization. Apply Q to
the three-field source identity in I.coherence, then hComp on Y. The intervening
inverse comparison pairs cancel. These equations hold on all objects by their
integral presentations and therefore are equations of natural transformations. -/
theorem rationalPurityCoherenceDescent
    (hLocalization : ∀ E : AdicPurityScalarNaturality.Field D C,
      source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E)
    (scalarLocalization : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (side : Bool),
      scalar D C I.scalarClosed E F h side ⋙
        Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side) ≅
      Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side) ⋙
        T D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side))
    (eta : ∀ E : AdicPurityScalarNaturality.Field D C, H D C f d E ≅ G D C f S E)
    (a : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      H D C f d E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ H D C f d F)
    (hEta :
  (∀ (E : AdicPurityScalarNaturality.Field D C) (K : Cat D C E Y),
      (hLocalization E).hom.app K ≫ (eta E).hom.app ((Q D C E Y).obj K) =
      (Q D C E X).map ((I.gamma E).hom.app K) ≫
        (gLocalization D C f S E).hom.app K) )
    (hA :
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      LocalizesComparison (hLocalization E) (hLocalization F)
      (scalarLocalization E F h true) (scalarLocalization E F h false)
      (I.a E F h) (a E F h)) )
    (hB :
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      LocalizesComparison (gLocalization D C f S E) (gLocalization D C f S F)
      (scalarLocalization E F h true) (scalarLocalization E F h false)
      (integralB D C f d S I E F h) (b D C f S E F h)) )
    (hUnit :
  (∀ (E : AdicPurityScalarNaturality.Field D C) (side : Bool)
      (K : Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)),
      (Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).map
        ((scalarUnit D C I.scalarClosed E side).hom.app K) =
      (scalarLocalization E E le_rfl side).hom.app K ≫
        (unit D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).hom.app
          ((Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).obj K)) )
    (hComp :
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
          ((Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)).obj K)) ) :
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (K : RCat D C E Y),
    (T D C E F h X).map ((eta E).hom.app K) ≫ (b D C f S E F h).hom.app K =
      (a E F h).hom.app K ≫ (eta F).hom.app ((T D C E F h Y).obj K)) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      UnitEquation (a E E le_rfl) (unit D C E X) (unit D C E Y)) ∧
  (∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
      CompositionEquation (a E F h) (a F L k) (a E L (h.trans k))
      (alpha D C E F L h k X) (alpha D C E F L h k Y)) := by sorry

end WeilConjectures.RationalScalarComparisonIdentification
