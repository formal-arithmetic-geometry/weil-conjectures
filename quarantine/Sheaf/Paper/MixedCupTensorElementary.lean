module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.MixedCupFieldNormalization
public import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-tensor-elementary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures.MixedCupCoefficientChange
open scoped WeilConjectures.MixedCupCoefficientChange

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)

/-- The prescribed scalar tensor component at this coefficient stage.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-tensor-elementary). -/
def FiniteTensorNormalized (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (tensorIso : ∀ {a b : Stage C} (f : Passage C a b), TensorComparison C S X f) : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields C.l C.Qbar)
    (n m : ℕ) (φ : Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1) →+*
      Padic.coefficientExtensionRing C.l (FieldAt C G) (m + 1))
    (K L : (domain C X.obj.left (.finite F n)).FullSubcategory),
    ((tensorIso (.finite φ) K L).hom).hom =
      (siteChange C X.obj.left (.finite φ)).map
        (eqToHom ((S F n).finiteTensorNormalization X K L) ≫
          (pullbackTensorFiniteModelIso C.l (FieldAt C F) X.obj.left n).inv.app
            (K.obj, L.obj)) ≫
      ((PurCompactSupport.scalarTensor_existsUnique
        ((constantSheaf (ProEt.topology X.obj.left) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ)))
        (pullbackTensorFiniteModel C.l (FieldAt C F) X.obj.left n)
        (pullbackTensorFiniteModel C.l (FieldAt C G) X.obj.left m)).exists.choose).hom.app
        (K.obj, L.obj) ≫
      (pullbackTensorFiniteModelIso C.l (FieldAt C G) X.obj.left m).hom.app
        (((change C X (.finite φ)).obj K).obj, ((change C X (.finite φ)).obj L).obj) ≫
      eqToHom ((S G m).finiteTensorNormalization X
        ((change C X (.finite φ)).obj K) ((change C X (.finite φ)).obj L)).symm

/-- The prescribed scalar tensor component at this coefficient stage.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-tensor-elementary). -/
def IntegralTensorNormalized (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (tensorIso : ∀ {a b : Stage C} (f : Passage C a b), TensorComparison C S X f) : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields C.l C.Qbar)
    (h : F ≤ G) [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    (K L : (domain C X.obj.left (.integral F)).FullSubcategory),
    ((tensorIso (.integral h) K L).hom).hom =
      (siteChange C X.obj.left (.integral h)).map
        (eqToHom (congrArg (fun T ↦ (T.obj K.obj).obj L.obj)
          ((S F 0).higher.integralTensorNormalization X))) ≫
      (integralTensorScalarComparison C.l (FieldAt C F) (FieldAt C G)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h)
        X.obj.left K.obj L.obj).hom ≫
      eqToHom (congrArg
        (fun T ↦ (T.obj ((change C X (.integral h)).obj K).obj).obj
          ((change C X (.integral h)).obj L).obj)
        ((S G 0).higher.integralTensorNormalization X)).symm

/-- The prescribed scalar tensor component at this coefficient stage.
Source: final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-tensor-elementary). -/
def RationalTensorNormalized (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (tensorIso : ∀ {a b : Stage C} (f : Passage C a b), TensorComparison C S X f) : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields C.l C.Qbar)
    (h : F ≤ G) [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    (K L : (domain C X.obj.left (.rational F)).FullSubcategory),
    ((tensorIso (.rational h) K L).hom).hom =
      (siteChange C X.obj.left (.rational h)).map
        (eqToHom (congrArg (fun T ↦ (T.obj K.obj).obj L.obj)
          ((S F 0).higher.rationalTensorNormalization X))) ≫
      (rationalTensorScalarComparison C.l (FieldAt C F) (FieldAt C G)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h)
        X.obj.left).hom.app (K.obj, L.obj) ≫
      eqToHom (congrArg
        (fun T ↦ (T.obj ((change C X (.rational h)).obj K).obj).obj
          ((change C X (.rational h)).obj L).obj)
        ((S G 0).higher.rationalTensorNormalization X)).symm


end WeilConjectures.MixedCupCoefficientChange
