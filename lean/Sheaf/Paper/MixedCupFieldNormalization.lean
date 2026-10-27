module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.MixedCupFieldOperations


/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-field-normalization).
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

/-- The field-stage arrows use exactly the recorded coefficient comparisons,
with the canonical point-fibre scalar and carrier identifications.
Source: proof steps 4 and 7 (blueprint: def-sf-mixed-cup-field-normalization). -/
def FieldCohomologyNormalized (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (uc : ∀ {a b : Stage C} (f : Passage C a b) (compact : Bool),
      cohomology C S X c compact a ⋙ pointChange C f ≅
        change C X f ⋙ cohomology C S X c compact b) : Prop :=
  (∀ (F G : Padic.FiniteCoefficientFields C.l C.Qbar) (h : F ≤ G) (compact : Bool)
    (K : (domain C X.obj.left (.rational F)).FullSubcategory),
    (uc (.rational h) compact).hom.app K =
      (rationalPoint C F G h
        ((if compact then (S F 0).higher.rational.support (sixFunctorStructure X) c
          else (S F 0).higher.rational.direct (sixFunctorStructure X)).obj K.obj)).hom ≫
        (rationalFibre C G).map (rationalOperation C S F G h X c compact K.obj).hom) ∧
  (∀ (F : Padic.FiniteCoefficientFields C.l C.Qbar) (compact : Bool)
    (K : (domain C X.obj.left (.rational F)).FullSubcategory),
    (uc (.closure F) compact).hom.app K =
      (closurePoint C F
        ((if compact then (S F 0).higher.rational.support (sixFunctorStructure X) c
          else (S F 0).higher.rational.direct (sixFunctorStructure X)).obj K.obj)).hom ≫
        (closedFibre C).map (closureOperation C S F X c compact K.obj).hom)

end WeilConjectures.MixedCupCoefficientChange
