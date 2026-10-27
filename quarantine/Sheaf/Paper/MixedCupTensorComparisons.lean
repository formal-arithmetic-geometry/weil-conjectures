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

/-- Normalized site tensor comparisons, independently of cohomology or cups.
Source: current blueprint mixed-support cup definition, final coefficient paragraph;
coefficient-change proof steps 2--4, 8 and 9.

Proof: At finite coefficients conjugate the canonical derived scalar balancing
isomorphism by the fixed finite tensor models and the datum's tensor equalities.
At an integral inclusion conjugate the completed tensor scalar comparison by
its recorded normalizations. At reduction take the canonical integral tensor
finite comparison on good flat K-flat representatives. Operation reduction makes
this arrow invertible; its universal representative equation proves the required
formula for every good pair, independently of choices. Rational inclusions are
the localization of the integral comparisons, and localization itself is the
identity on the prescribed tensor object with its equality transports. For
closure represent the inverse common-stage tensor comparison at the input
field, inserting the specified transition unitors. Enlargement of the common
field gives the same morphism class. Each elementary map is natural in both
inputs by its representative construction. The identity passage has the identity
tensor map. Define a formal composite by applying the second scalar functor to
the first tensor map and then the second tensor map. Naturality is preserved by
this operation. Induction on passages gives exactly the displayed identity and
composition equations and all six elementary normalization predicates.
(blueprint: lem-sf-mixed-cup-tensor-comparisons). -/
theorem tensorComparisons_exists (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] :
    ∃ tensorIso : ∀ {a b : Stage C} (f : Passage C a b), TensorComparison C S X f,
      (FiniteTensorNormalized C S X tensorIso) ∧
      (IntegralTensorNormalized C S X tensorIso) ∧
      (RationalTensorNormalized C S X tensorIso) ∧
      (ReductionTensorNormalized C S X tensorIso) ∧
      (LocalizationTensorNormalized C S X tensorIso) ∧
      (ClosureTensorNormalized C S X tensorIso) ∧
      (∀ {a b : Stage C} (f : Passage C a b)
    {K K' L L' : (domain C X.obj.left a).FullSubcategory} (k : K ⟶ K') (l : L ⟶ L'),
    (change C X f).map (tensorMap C S X a k l) ≫ (tensorIso f K' L').hom =
      (tensorIso f K L).hom ≫
      tensorMap C S X b ((change C X f).map k) ((change C X f).map l)) ∧
      (∀ (a : Stage C) (K L : (domain C X.obj.left a).FullSubcategory),
    (tensorIso (.identity a) K L).hom = 𝟙 _) ∧
      (∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d)
    (K L : (domain C X.obj.left a).FullSubcategory),
    (tensorIso (.comp f g) K L).hom =
      (change C X g).map ((tensorIso f K L).hom) ≫
      (tensorIso g ((change C X f).obj K) ((change C X f).obj L)).hom) := by
  sorry

end WeilConjectures.MixedCupCoefficientChange
