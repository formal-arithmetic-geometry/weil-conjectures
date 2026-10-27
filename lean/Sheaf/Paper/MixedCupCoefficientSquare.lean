module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.MixedCupTensorNormalization
public import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: prop-sf-mixed-cup-coefficient-change).
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

/-- The cup square for normalized operation and tensor comparisons.
Source: current blueprint mixed-support cup definition, displayed projection/counit
composite and final coefficient sentence; coefficient-change proof steps 5--9.

Proof: First treat elementary passages. The ordinary comparison is the normalized
mate of scalar/pullback, so its composite with the new ordinary counit equals
the scalar image of the old counit after the pullback comparison. For finite
coefficients this is the counit-transpose characterization; reduction preserves
the adjunction maps, and for finite-free integral extension the same identity
can be checked after restriction in a finite basis. Tensor this mate equation
with the first input. Coefficient/projection compatibility gives the scalar
square for the projection transformation. Its naturality in the second argument
applies to the ordinary comparison on L. Paste it with the tensor/counit square
and use naturality of the support comparison. The middle pullback of the ordinary
comparison cancels by the mate equation. Apply the exact point fibre. Its
normalized tensor and scalar/sections identifications give exactly pointTensor
and the cohomology components in the displayed equality. The elementary
normalization hypotheses fix these maps, so arbitrary automorphisms cannot be
substituted. Rationalization preserves the equality; at closure represent the
finite diagram over a common field. For the identity passage use the point
unitor and identity tensor map. For a composite paste the two squares: naturality
of pointTensor and the second cohomology comparison, together with the specified
point associator, identify the source composites, while tensor naturality and
the two composition equations identify the target composites. This proves the
claim by induction on the formal passage.
(blueprint: lem-sf-mixed-cup-square). -/
theorem normalizedCup_coefficient_square (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (pointUnit : ∀ a : Stage C, pointChange C (.identity a) ≅ 𝟭 _)
    (pointComp : ∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d),
    pointChange C (.comp f g) ≅ pointChange C f ⋙ pointChange C g)
    (cohomologyIso : ∀ {a b : Stage C} (f : Passage C a b) (compact : Bool),
    cohomology C S X c compact a ⋙ pointChange C f ≅
      change C X f ⋙ cohomology C S X c compact b)
    (tensorIso : ∀ {a b : Stage C} (f : Passage C a b), TensorComparison C S X f)
    (pointUnit_normalized : ∀ a, PointUnitNormalized C a (pointUnit a))
    (pointComp_normalized : ∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d),
    PointCompNormalized C f g (pointComp f g))
    (ringed_cohomology_normalized : RingedCohomologyNormalized C S X c cohomologyIso)
    (localization_cohomology_normalized : LocalizationCohomologyNormalized C S X c cohomologyIso)
    (field_cohomology_normalized : FieldCohomologyNormalized C S X c cohomologyIso)
    (identity : ∀ (a : Stage C) (compact : Bool)
    (K : (domain C X.obj.left a).FullSubcategory),
    (cohomologyIso (.identity a) compact).hom.app K =
      (pointUnit a).hom.app ((cohomology C S X c compact a).obj K))
    (composition : ∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d)
    (compact : Bool) (K : (domain C X.obj.left a).FullSubcategory),
    (cohomologyIso (.comp f g) compact).hom.app K =
      (pointComp f g).hom.app ((cohomology C S X c compact a).obj K) ≫
      (pointChange C g).map ((cohomologyIso f compact).hom.app K) ≫
      (cohomologyIso g compact).hom.app ((change C X f).obj K))
    (finite_tensor_normalized : FiniteTensorNormalized C S X tensorIso)
    (integral_tensor_normalized : IntegralTensorNormalized C S X tensorIso)
    (rational_tensor_normalized : RationalTensorNormalized C S X tensorIso)
    (reduction_tensor_normalized : ReductionTensorNormalized C S X tensorIso)
    (localization_tensor_normalized : LocalizationTensorNormalized C S X tensorIso)
    (closure_tensor_normalized : ClosureTensorNormalized C S X tensorIso)
    (tensor_natural : ∀ {a b : Stage C} (f : Passage C a b)
    {K K' L L' : (domain C X.obj.left a).FullSubcategory} (k : K ⟶ K') (l : L ⟶ L'),
    (change C X f).map (tensorMap C S X a k l) ≫ (tensorIso f K' L').hom =
      (tensorIso f K L).hom ≫
      tensorMap C S X b ((change C X f).map k) ((change C X f).map l))
    (tensor_identity : ∀ (a : Stage C) (K L : (domain C X.obj.left a).FullSubcategory),
    (tensorIso (.identity a) K L).hom = 𝟙 _)
    (tensor_composition : ∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d)
    (K L : (domain C X.obj.left a).FullSubcategory),
    (tensorIso (.comp f g) K L).hom =
      (change C X g).map ((tensorIso f K L).hom) ≫
      (tensorIso g ((change C X f).obj K) ((change C X f).obj L)).hom)
    : ∀ {a b : Stage C} (f : Passage C a b)
    (K L : (domain C X.obj.left a).FullSubcategory),
    (pointChange C f).map (normalizedCup C S X c a K L) ≫
      (cohomologyIso f true).hom.app (tensorInput C S X a K L) ≫
      (cohomology C S X c true b).map ((tensorIso f K L).hom) =
      (pointTensor C f ((cohomology C S X c true a).obj K)
        ((cohomology C S X c false a).obj L)).hom ≫
      ((cohomologyIso f true).hom.app K ⊗ₘ (cohomologyIso f false).hom.app L) ≫
      normalizedCup C S X c b ((change C X f).obj K) ((change C X f).obj L) := by
  sorry

end WeilConjectures.MixedCupCoefficientChange
