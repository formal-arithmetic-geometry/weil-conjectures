module

public import Sheaf.Paper.MixedCupFieldCoordinates
public import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-field-operations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures.MixedCupCoefficientChange
open scoped WeilConjectures.MixedCupCoefficientChange
variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)

attribute [local irreducible] rationalOperationBridge integralOperationBridge
  localizationOperation

universe v w v' w'

/-- Select the two operation comparisons without unfolding their coefficient categories.
Source: proof step 4 (blueprint: def-sf-mixed-cup-field-operations). -/
def selectCoefficientComparison
    {B : SixFunctorSpace D → Type v} [∀ Y, Category.{w} (B Y)]
    {B' : SixFunctorSpace D → Type v'} [∀ Y, Category.{w'} (B' Y)]
    {T : SixFunctorPushStage D B} {T' : SixFunctorPushStage D B'}
    {L : ∀ Y, B Y ⥤ B' Y} (e : SixFunctorCoefficientComparison T T' L)
    {Y Z : SixFunctorSpace D} (f : Y ⟶ Z)
    (c : Compactification f.hom.left) (compact : Bool) :
    (if compact then T.support f c else T.direct f) ⋙ L Z ≅
      L Y ⋙ (if compact then T'.support f c else T'.direct f) :=
  match compact with
  | true => (e.supportAdjunction f c).left
  | false => (e.directAdjunction f).right

/-- The recorded finite-field comparison with the same support choice on both sides.
Source: proof step 4 (blueprint: def-sf-mixed-cup-field-operations). -/
def fieldOperationComparison (S : Operations C)
    (F G : Padic.FiniteCoefficientFields C.l C.Qbar) (h : F ≤ G)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (compact : Bool) :=
  selectCoefficientComparison ((commonOperations C S).coefficientTransition h)
    (sixFunctorStructure X) c compact

/-- The recorded common-stage comparison with the same support choice on both sides.
Source: proof step 4 (blueprint: def-sf-mixed-cup-field-operations). -/
def closureOperationComparison (S : Operations C)
    (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (compact : Bool) :=
  selectCoefficientComparison ((commonOperations C S).commonStageComparison F)
    (sixFunctorStructure X) c compact

attribute [local irreducible] fieldOperationComparison closureOperationComparison

/-- Recorded field transition for either support choice.
Source: proof step 4 (blueprint: def-sf-mixed-cup-field-operations). -/
def rationalOperation (S : Operations C)
    (F G : Padic.FiniteCoefficientFields C.l C.Qbar) (h : F ≤ G)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (compact : Bool)
    (K : sfRationalConstructibleCategory C.l (FieldAt C F) X.obj.left) :
    (siteChange C (Spec (.of D.k)) (.rational h)).obj
      ((if compact then (S F 0).higher.rational.support (sixFunctorStructure X) c
        else (S F 0).higher.rational.direct (sixFunctorStructure X)).obj K) ≅
    ((if compact then (S G 0).higher.rational.support (sixFunctorStructure X) c
      else (S G 0).higher.rational.direct (sixFunctorStructure X)).obj
      ((siteChange C X.obj.left (.rational h)).obj K)) :=
  (siteChange C (Spec (.of D.k)) (.rational h)).mapIso
    (rationalOperationBridge C F (S F 0).higher ((commonOperations C S).coefficientStages F)
      X c compact K) ≪≫
  (operationStageTransitionIso C.l C.Qbar
    (Spec (.of D.k)) F G h).symm.app
      ((if compact then ((commonOperations C S).coefficientStages F).rational.support
        (sixFunctorStructure X) c else ((commonOperations C S).coefficientStages F).rational.direct
          (sixFunctorStructure X)).obj K) ≪≫
  (fieldOperationComparison C S F G h X c compact).app K ≪≫
  (if compact then ((commonOperations C S).coefficientStages G).rational.support
      (sixFunctorStructure X) c else ((commonOperations C S).coefficientStages G).rational.direct
        (sixFunctorStructure X)).mapIso
    ((operationStageTransitionIso C.l C.Qbar X.obj.left F G h).app K) ≪≫
  rationalOperationBridge C G ((commonOperations C S).coefficientStages G) (S G 0).higher
    X c compact ((siteChange C X.obj.left (.rational h)).obj K)

/-- Recorded inclusion comparison for either support choice.
Source: proof step 4 (blueprint: def-sf-mixed-cup-field-operations). -/
def closureOperation (S : Operations C)
    (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (compact : Bool)
    (K : sfRationalConstructibleCategory C.l (FieldAt C F) X.obj.left) :=
  (siteChange C (Spec (.of D.k)) (.closure F)).mapIso
    (rationalOperationBridge C F (S F 0).higher ((commonOperations C S).coefficientStages F)
      X c compact K) ≪≫
  (closureOperationComparison C S F X c compact).app K


end WeilConjectures.MixedCupCoefficientChange
