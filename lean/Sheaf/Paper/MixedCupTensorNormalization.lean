module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.MixedCupTensorClosure
public import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-tensor-normalization).
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

/-- Good integral representatives reduce to flat K-flat finite representatives.
Source: proof step 3; Stacks 06YY
(blueprint: def-sf-mixed-cup-tensor-normalization).
Proof: the quotient functor is scalar extension. Extension of scalars preserves
flat modules and K-flat complexes by tensor associativity and exact restriction.
Apply this termwise to the recorded good representative predicate. -/
theorem reducedGood (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (W : Scheme.{u}) (n : ℕ)
    (P : (integralOperationsGoodComplex C.l (FieldAt C F) W).FullSubcategory) :
    proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf C.l (FieldAt C F) W n)
      ((unrestrictedIntegralFiniteComplex C.l (FieldAt C F) W n).obj P.obj) := by
  let R := completedIntegralCommRingSheafUnrestricted C.l (FieldAt C F) W
  let S := integralCoefficientCommRingSheaf C.l (FieldAt C F) W n
  let E := unrestrictedIntegralReductionFunctor C.l (FieldAt C F) W n
  let φ := completedIntegralCommRingProjectionUnrestricted C.l (FieldAt C F) W n
  have : E.Additive :=
    unrestrictedIntegralReductionFunctor_additive C.l (FieldAt C F) W n
  have ho (M : integralTowerModules C.l (FieldAt C F) W) :
      E.obj M = SheafOfModules.changeOfRings φ M :=
    (unrestrictedIntegralReductionExistence C.l (FieldAt C F) W n).choose_spec.choose M
  have hm {M N : integralTowerModules C.l (FieldAt C F) W} (g : M ⟶ N) :
      E.map g = eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom φ M g ≫
        eqToHom (ho N).symm :=
    (unrestrictedIntegralReductionExistence C.l (FieldAt C F) W n).choose_spec.choose_spec.choose g
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  have hflat (i : ℤ) : exactFunctor _ _
      (@tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.obj.X i)) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.obj.X i)) (P.property.2 i)
  obtain ⟨hk, hf⟩ :=
    SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      φ P.obj E ho hm P.property.1 hflat
  refine ⟨?_, ?_⟩
  · exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk
  · intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso S _).symm (hf i)

/-- A finite quotient tensor component is fixed by the actual Roos projection,
with the two reduced K-flat representative comparisons inserted.
Source: proof steps 3 and 9 (blueprint: def-sf-mixed-cup-tensor-normalization). -/
def ReductionTensorNormalized (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (t : ∀ {a b : Stage C} (f : Passage C a b), TensorComparison C S X f) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields C.l C.Qbar) (n : ℕ)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    (K L : (domain C X.obj.left (.integral F)).FullSubcategory)
    (P Q : (integralOperationsGoodComplex C.l (FieldAt C F) X.obj.left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj.obj)
    (d : DerivedCategory.Q.obj Q.obj ≅ L.obj.obj),
    HEq
      (((t (.reduction F n) K L).hom).hom ≫
        eqToHom ((S F n).finiteTensorNormalization X
          ((change C X (.reduction F n)).obj K) ((change C X (.reduction F n)).obj L)) ≫
        (finiteIntrinsicDerivedTensor C.l (FieldAt C F) X.obj.left n).map
          (Prod.mkHom
            (sixFunctorIntegralReductionModel C (FieldAt C F) n X K.obj P e).hom
            (sixFunctorIntegralReductionModel C (FieldAt C F) n X L.obj Q d).hom) ≫
        (pullbackTensorFiniteModelIso C.l (FieldAt C F) X.obj.left n).inv.app
          (DerivedCategory.Q.obj
            ((unrestrictedIntegralFiniteComplex C.l (FieldAt C F) X.obj.left n).obj P.obj),
           DerivedCategory.Q.obj
            ((unrestrictedIntegralFiniteComplex C.l (FieldAt C F) X.obj.left n).obj Q.obj)) ≫
        (pullbackTensorFiniteModel C.l (FieldAt C F) X.obj.left n).representative.inv.app
          (⟨_, reducedGood C F X.obj.left n P⟩, ⟨_, reducedGood C F X.obj.left n Q⟩))
      ((scalarReductionDerivedExtension C.l (FieldAt C F) X.obj.left n).map
          (eqToHom (congrArg (fun T ↦ ((T.obj K.obj).obj L.obj).obj)
            ((S F 0).higher.integralTensorNormalization X))) ≫
        integralTensorFiniteComparison C.l (FieldAt C F) X.obj.left K.obj.obj L.obj.obj
          P Q e d n)

/-- Raw localization leaves tensor objects unchanged. Its component is the identity
on that prescribed localized integral object, with equality transports expressed by HEq.
Source: proof step 4 (blueprint: def-sf-mixed-cup-tensor-normalization). -/
def LocalizationTensorNormalized (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (t : ∀ {a b : Stage C} (f : Passage C a b), TensorComparison C S X f) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (K L : (domain C X.obj.left (.integral F)).FullSubcategory),
    HEq ((t (.localization F) K L).hom).hom
      (𝟙 ((siteChange C X.obj.left (.localization F)).obj
        (tensorInput C S X (.integral F) K L).obj))


end WeilConjectures.MixedCupCoefficientChange
