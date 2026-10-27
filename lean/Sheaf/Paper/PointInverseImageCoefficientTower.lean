/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.IsomorphismComparisonScalarExtension
public import Sheaf.Paper.IsomorphismScalarTensorKFlatModel
public import Sheaf.Paper.PointDerivedTensorTowerCoherence
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IsomorphismDerivedPullback
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.PointProEtaleSectionsExactOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic

/-! # Inverse-image coefficient towers at the geometric point

Source: blueprint main-20261015, def-weil-global-geometric-frobenius,
returned transport proof steps 5--6; the explicit coefficient calculation is agent-written.
(blueprint: lem-weil-point-inverse-image-coefficient-tower).

Ordinary tensor is the universal derived functor. Its tensor comparison is
transported from the exact model by the existing uniquely counit-normalized
isomorphism. No replacement comparison is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
namespace WeilConjectures.PointInverseImageCoefficientTower

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
  (hunit : ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x))
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

/-- The specified ordinary inverse-image tensor comparison, transported through
its uniquely counit-normalized identification with universal derived tensor.
Source: blueprint main-20261015, global geometric Frobenius transport steps 5--6
(blueprint: lem-weil-point-inverse-image-coefficient-tower). -/
def ordinaryComparison (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (completedDerivedScalarExtension l E L ι (Spec (.of D.k))).obj
        ((inverseImageIntegralDerived l E g).obj K) ≅
      (inverseImageIntegralDerived l L g).obj
        ((completedDerivedScalarExtension l E L ι (Spec (.of D.k))).obj K) :=
  ((isomorphismScalarModel_existsUnique l E L ι (Spec (.of D.k))).exists.choose.app
      ((inverseImageIntegralDerived l E g).obj K)).symm ≪≫
    (isomorphismScalarTensorDerived l E L ι g).app K ≪≫
    (inverseImageIntegralDerived l L g).mapIso
      ((isomorphismScalarModel_existsUnique l E L ι (Spec (.of D.k))).exists.choose.app K)

/-- Psi is exactly sections of beta inverse followed by the specified phi at G_E K.
Source: blueprint main-20261015, global geometric Frobenius transport steps 5--6
(blueprint: lem-weil-point-inverse-image-coefficient-tower). -/
def sectionsComparison
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    (pointCompletedDerivedSections D.k l L).obj
        ((inverseImageIntegralDerived l L g).obj
          ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K)) ≅
      (pointIntegralModuleDerivedTensor l E L ι).obj
        ((pointCompletedDerivedSections D.k l E).obj
          ((inverseImageIntegralDerived l E g).obj K)) :=
  ((pointCompletedDerivedSections D.k l L).mapIso
    ((scalarCompletionIso l E L ι (Spec (.of D.k))
      ((inverseImageIntegralDerived l E g).obj K)
      (isomorphismComparisonInputs_constructible l E g hunit hunit K hK).1.1).symm ≪≫
      (isomorphismScalarTensorDerived l E L ι g).app K ≪≫
      (inverseImageIntegralDerived l L g).mapIso
        (scalarCompletionIso l E L ι (Spec (.of D.k)) K hK.1))).symm ≪≫
    pointSectionsScalarExtensionIso l E L ι D hl
      ((inverseImageIntegralDerived l E g).obj K)
      ((pointIntegralConstructible_iff l E D hl
        ((inverseImageIntegralDerived l E g).obj K)).mpr
        (isomorphismComparisonInputs_constructible l E g hunit hunit K hK).1)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The seven clauses of ordinary, local, completed and sections coherence.
Beta is exactly isomorphismComparisonScalarBeta. Each sectionsComparison is sections
of the inverse of its defining chi-b-chi composite followed by the specified phi.
The associator and unit are exactly pointIntegralScalarAssoc and pointIntegralScalarUnit.
Source: blueprint main-20261015, global geometric Frobenius transport steps 5--6
(blueprint: lem-weil-point-inverse-image-coefficient-tower). -/
structure Laws : Prop where
  ordinary_tower :
    ∀ K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))), (pointDerivedTensorAssoc
      D.k l E L ι M j).hom.app ((inverseImageIntegralDerived l E g).obj K) ≫ (ordinaryComparison
      D l g E M (j.comp ι) K).hom = (completedDerivedScalarExtension l L M j (Spec (.of
      D.k))).map ((ordinaryComparison D l g E L ι K).hom) ≫ (ordinaryComparison D l g L M j
      ((completedDerivedScalarExtension l E L ι (Spec (.of D.k))).obj K)).hom ≫
      (inverseImageIntegralDerived l M g).map ((pointDerivedTensorAssoc D.k l E L ι M j).hom.app
      K)
  ordinary_unit :
    ∀ K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))), (ordinaryComparison D l g
      E E (AlgHom.id ℚ_[l] E) K).hom ≫ (inverseImageIntegralDerived l E g).map
      ((pointDerivedTensorUnit D.k l E).hom.app K) = (pointDerivedTensorUnit D.k l E).hom.app
      ((inverseImageIntegralDerived l E g).obj K)
  local_formula :
    ∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) (i : ℤ) (U :
      (Spec (.of D.k)).ProEt) (a0 : (completedIntegralCommRingSheafUnrestricted l L (Spec (.of
      D.k))).obj.obj (op ((proEtaleIsoPostcompose g).obj U))) (b0 :
      (completedIntegralCommRingSheafUnrestricted l M (Spec (.of D.k))).obj.obj (op
      ((proEtaleIsoPostcompose g).obj U))) (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose
      g).obj U))), ((integralOrdinaryScalarComp l E L ι (Spec (.of D.k)) M j).hom.app
      ((inverseImageIntegralModules l E g).obj (P.obj.X i)) ≫ (isomorphismScalarTensor l E M
      (j.comp ι) g).hom.app (P.obj.X i)).val.app (op U) (integralOrdinaryTensorSection l L M j
      (Spec (.of D.k)) ((integralOrdinaryScalar l E L ι (Spec (.of D.k))).obj
      ((inverseImageIntegralModules l E g).obj (P.obj.X i))) (op U)
      ((inverseImageCompletedCoefficientMap l M g).hom.app (op U) b0)
      (integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) ((inverseImageIntegralModules l E
      g).obj (P.obj.X i)) (op U) ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) a0)
      x)) = (integralOrdinaryTensorSection l E M (j.comp ι) (Spec (.of D.k)) (P.obj.X i) (op
      ((proEtaleIsoPostcompose g).obj U)) (b0 * (integralCompletedScalarMap l L M j (Spec (.of
      D.k))).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a0) x) ∧ ((integralOrdinaryScalar l
      L M j (Spec (.of D.k))).map ((isomorphismScalarTensor l E L ι g).hom.app (P.obj.X i)) ≫
      (isomorphismScalarTensor l L M j g).hom.app ((integralOrdinaryScalar l E L ι (Spec (.of
      D.k))).obj (P.obj.X i)) ≫ (inverseImageIntegralModules l M g).map
      ((integralOrdinaryScalarComp l E L ι (Spec (.of D.k)) M j).hom.app (P.obj.X i))).val.app
      (op U) (integralOrdinaryTensorSection l L M j (Spec (.of D.k)) ((integralOrdinaryScalar l
      E L ι (Spec (.of D.k))).obj ((inverseImageIntegralModules l E g).obj (P.obj.X i))) (op U)
      ((inverseImageCompletedCoefficientMap l M g).hom.app (op U) b0)
      (integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) ((inverseImageIntegralModules l E
      g).obj (P.obj.X i)) (op U) ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) a0)
      x)) = (integralOrdinaryTensorSection l E M (j.comp ι) (Spec (.of D.k)) (P.obj.X i) (op
      ((proEtaleIsoPostcompose g).obj U)) (b0 * (integralCompletedScalarMap l L M j (Spec (.of
      D.k))).hom.app (op ((proEtaleIsoPostcompose g).obj U)) a0) x)
  completed_tower :
    ∀ (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) (hK :
      sfIntegralConstructible l E (Spec (.of D.k)) K), (pointIntegralScalarAssoc l E L ι M j D
      hl ((inverseImageIntegralDerived l E g).obj K) ((pointIntegralConstructible_iff l E D hl
      ((inverseImageIntegralDerived l E g).obj K)).mpr
      (isomorphismComparisonInputs_constructible l E g hunit hunit K hK).1)).hom ≫
      isomorphismComparisonScalarBeta l E M (j.comp ι) g hunit hunit K hK =
      (integralScalarExtension l L M j (Spec (.of D.k))).map (isomorphismComparisonScalarBeta l
      E L ι g hunit hunit K hK) ≫ isomorphismComparisonScalarBeta l L M j g hunit hunit
      ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K)
      (sfIntegralScalarExtension_constructible D.p l hl E L ι (Spec (.of D.k)) K hK) ≫
      (inverseImageIntegralDerived l M g).map ((pointIntegralScalarAssoc l E L ι M j D hl K
      ((pointIntegralConstructible_iff l E D hl K).mpr hK)).hom)
  sections_tower :
    ∀ (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) (hK :
      sfIntegralConstructible l E (Spec (.of D.k)) K), (pointCompletedDerivedSections D.k l
      M).map ((inverseImageIntegralDerived l M g).map ((pointIntegralScalarAssoc l E L ι M j D
      hl K ((pointIntegralConstructible_iff l E D hl K).mpr hK)).hom)) ≫ (sectionsComparison D l
      hl g hunit E M (j.comp ι) K hK).hom = (sectionsComparison D l hl g hunit L M j
      ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K)
      (sfIntegralScalarExtension_constructible D.p l hl E L ι (Spec (.of D.k)) K hK)).hom ≫
      (pointIntegralModuleDerivedTensor l L M j).map (sectionsComparison D l hl g hunit E L ι K
      hK).hom ≫ (pointIntegralModuleDerivedAssoc l E L ι M j).hom.app
      ((pointCompletedDerivedSections D.k l E).obj ((inverseImageIntegralDerived l E g).obj K))
  completed_unit :
    ∀ (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) (hK :
      sfIntegralConstructible l E (Spec (.of D.k)) K), isomorphismComparisonScalarBeta l E E
      (AlgHom.id ℚ_[l] E) g hunit hunit K hK ≫ (inverseImageIntegralDerived l E g).map
      ((pointIntegralScalarUnit l E D hl K ((pointIntegralConstructible_iff l E D hl K).mpr
      hK)).hom) = (pointIntegralScalarUnit l E D hl ((inverseImageIntegralDerived l E g).obj K)
      ((pointIntegralConstructible_iff l E D hl ((inverseImageIntegralDerived l E g).obj K)).mpr
      (isomorphismComparisonInputs_constructible l E g hunit hunit K hK).1)).hom
  sections_unit :
    ∀ (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) (hK :
      sfIntegralConstructible l E (Spec (.of D.k)) K), (sectionsComparison D l hl g hunit E E
      (AlgHom.id ℚ_[l] E) K hK).hom ≫ (pointIntegralModuleDerivedUnit l E).hom.app
      ((pointCompletedDerivedSections D.k l E).obj ((inverseImageIntegralDerived l E g).obj K))
      = (pointCompletedDerivedSections D.k l E).map ((inverseImageIntegralDerived l E g).map
      ((pointIntegralScalarUnit l E D hl K ((pointIntegralConstructible_iff l E D hl K).mpr
      hK)).hom))

end WeilConjectures.PointInverseImageCoefficientTower
namespace WeilConjectures

/-- The specified inverse-image comparisons satisfy all coefficient tower and unit laws.
Source: blueprint main-20261015, def-weil-global-geometric-frobenius, returned
transport proof steps 5--6 (blueprint: lem-weil-point-inverse-image-coefficient-tower).

Proof:
1. Choose a flat-term K-flat resolution (lem-pc-kflat-resolution). The tensor model
of lem-weil-isomorphism-scalar-tensor-kflat-model and the multiplication associators
of lem-weil-point-derived-tensor-tower-coherence compute both ordinary routes on
one representative. Both send the local double tensor to g inverse of x tensor a0*b0.
The coefficient maps commute with inclusions: compare every quotient projection,
using lem-weil-proetale-isomorphism-inverse-image and the defining projections of
c in def-weil-inverse-image-pullback-comparison. Local tensor generation and
sheafification give equality of chain maps. Localization gives the unbounded law.
The exact finite-free model has the same normalized tensor generators and counits.
The unique isomorphism in isomorphismScalarModel_existsUnique transports its b
to the universal derived tensor used in ordinary_tower and ordinary_unit.
Multiplication gives the ordinary unit law.
2. The objects G K and T K stay constructible and complete by
lem-weil-isomorphism-derived-pullback and
lem-weil-integral-scalar-extension-constructible. Thus the prescribed completion
comparisons are invertible (lem-weil-finite-free-completed-scalar-comparison).
3. Put U = chi_2 at T_1 K after C_2(chi_1 at K). Precompose the completed tower
with U at G K. Substitute beta = G(chi) b chi inverse. Naturality of chi_2 at
beta_1 and of b_2 at chi_1 cancels adjacent inverse pairs. The two routes become
the ordinary tower, followed by G(chi_3). Cancel U. This is exactly the associator
of lem-weil-point-sections-scalar-extension, with no new choice of maps.
4. Invert and rearrange that identity and apply exact derived sections
(lem-weil-point-proetale-sections-exact). Substitute psi = phi_G Gamma(beta inverse).
The phi tower law of lem-weil-point-sections-scalar-extension and its naturality
at beta_1 inverse give the asserted module associator equation.
5. At the identity extension u chi = multiplication. Substitute into beta and use
the ordinary unit law to get G(u) beta = u_G. The phi unit law then gives the
psi unit equation. The stalk-unit witness is supplied by the finite-field datum:
charP_of_card_eq_prime_pow identifies characteristic p on k0, a distinct prime l
is a nonzero unit, and the inclusion, affine global-section map and germs preserve it.
-/
theorem point_inverse_image_coefficient_tower
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (Q : Type u) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] :
    ∃ hunit : ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x),
      ∀ (E L M : Padic.FiniteCoefficientFields l Q) (hEL : E ≤ L) (hLM : L ≤ M),
        PointInverseImageCoefficientTower.Laws D l hl g hunit E.val L.val
          (IntermediateField.inclusion hEL) M.val (IntermediateField.inclusion hLM) := by
  sorry

end WeilConjectures
