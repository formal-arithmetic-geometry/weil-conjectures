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

/-- Normalized operation comparisons, without a cup or site tensor comparison.
Source: current blueprint mixed-support cup definition, final coefficient paragraph;
coefficient-change proof steps 2--5, 7 and 8.

Proof: For finite coefficients use the ordinary counit-transpose scalar mate and
its invertibility on finite-Tor etale-origin inputs. For support use the proper
scalar comparison followed by the open balancing isomorphism, and transport the
etale construction through the canonical site comparison. For integral reduction
use the operation reduction maps; for integral extension use the finite-free
completed scalar comparison. Its ordinary direct-image mate is invertible: after
restriction and a finite basis it is the finite direct sum of the old direct
image. Restriction reflects invertibility. These are checks of the canonical
maps, so they do not introduce a basis choice. Conjugate by the actual operation
coordinates, apply exact point sections and the prescribed scalar/sections map.
Rationalize the integral comparisons, then represent closure comparisons over a
common finite field. Their naturality gives natural isomorphisms. Define the
identity component by the normalized point unitor, and define the component of
a formal composite by the displayed three-map composite. The elementary
normalization predicates then hold by construction. The point unitor and
associator descend from ordinary scalar balancing on K-flat complexes; scalar
extension preserves K-flatness. Their universal counit equations give the two
point normalization predicates. This proves the displayed identity and formal
composition laws without asserting a new cup square.
(blueprint: lem-sf-mixed-cup-operation-comparisons). -/
theorem operationComparisons_exists (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left) :
    ∃ pointUnit : ∀ a : Stage C, pointChange C (.identity a) ≅ 𝟭 _,
    ∃ pointComp : ∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d),
    pointChange C (.comp f g) ≅ pointChange C f ⋙ pointChange C g,
    ∃ cohomologyIso : ∀ {a b : Stage C} (f : Passage C a b) (compact : Bool),
    cohomology C S X c compact a ⋙ pointChange C f ≅
      change C X f ⋙ cohomology C S X c compact b,
      (∀ a, PointUnitNormalized C a (pointUnit a)) ∧
      (∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d),
    PointCompNormalized C f g (pointComp f g)) ∧
      (RingedCohomologyNormalized C S X c cohomologyIso) ∧
      (LocalizationCohomologyNormalized C S X c cohomologyIso) ∧
      (FieldCohomologyNormalized C S X c cohomologyIso) ∧
      (∀ (a : Stage C) (compact : Bool)
    (K : (domain C X.obj.left a).FullSubcategory),
    (cohomologyIso (.identity a) compact).hom.app K =
      (pointUnit a).hom.app ((cohomology C S X c compact a).obj K)) ∧
      (∀ {a b d : Stage C} (f : Passage C a b) (g : Passage C b d)
    (compact : Bool) (K : (domain C X.obj.left a).FullSubcategory),
    (cohomologyIso (.comp f g) compact).hom.app K =
      (pointComp f g).hom.app ((cohomology C S X c compact a).obj K) ≫
      (pointChange C g).map ((cohomologyIso f compact).hom.app K) ≫
      (cohomologyIso g compact).hom.app ((change C X f).obj K)) := by
  sorry

end WeilConjectures.MixedCupCoefficientChange
