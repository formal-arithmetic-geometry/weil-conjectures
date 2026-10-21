/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.Paper.CoefficientTwistsDetailed
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Paper.PurInverseImageCompatibleFreeTower
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
import Sheaf.Paper.CartesianCoefficientTwists
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.TateTwistLocallyFree

/-! # Inverse image of the completed integral Tate line

Source: main-20261015 blueprint, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, Roots of unity and Integral twist
(blueprint: lem-pur-integral-twist-line-inverse-image).

The adjunction expresses local section formulas on the original site: the adjunct of
`rho` sends a root tensor to the pulled-back root tensor and is semilinear over the
adjunct of `alpha`. Thus no section of an inverse image is treated as a section on the
source site. Level `n` always means positive exponent `n + 1`.

## Main definitions and statement

* `IsPurIntegralCoefficientComparison`: the coefficient projection characterization.
* `IsPurRootLimitComparison`: the roots-of-unity projection characterization.
* `IsPurIntegralTwistComparison`: the tensor formula and completed semilinearity.
* `pur_integral_twist_line_inverse_image`: the isomorphisms and both naturality squares.

The coefficient and root comparison predicates below are projection-level
characterizations.  In particular, their quantification over every finite level
keeps the completed objects tied to the canonical inverse-limit constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace AlgebraicGeometry.Scheme

/-- The underlying abelian sheaf of the recorded completed integral twist module.
Source: Integral twist paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
abbrev purIntegralTwistAb (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  (SheafOfModules.toSheaf _).obj (purTwistIntegralModule S l E)

/-- The underlying abelian map of the existing canonical coefficient inclusion at twist one.
Source: Integral twist paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
def purIntegralTwistScalarMap (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [∀ x : S, Invertible (l : S.residueField x)]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (ι : E →ₐ[ℚ_[l]] F) :
    purIntegralTwistAb S l E ⟶ purIntegralTwistAb S l F :=
  ⟨(PresheafOfModules.toPresheaf _).map (twistScalarMaps l E S F ι 1).val⟩

/-- The defining finite-projection equations for the completed coefficient comparison.
The constant comparison is the recorded constant-section adjunct, with commutativity retained.
Source: Integral twist paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
def IsPurIntegralCoefficientComparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (α : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X) : Prop :=
  ∀ n : ℕ, α ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
        proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The root-limit comparison is fixed by every root projection.
Source: Roots of unity paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
def IsPurRootLimitComparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    (l : ℕ) [Fact l.Prime]
    (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l) : Prop :=
  ∀ n : ℕ,
    τ ≫ limit.π (proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) =
      (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)) (op n)) ≫
          proEtaleRootsOfUnityInverseImageMap h (l ^ (n + 1))

/-- The local tensor formula and completed semilinearity, expressed under the actual
inverse-image/direct-image adjunction. The formula is stated for all local scalar sections;
for a constant scalar its direct-image comparison is the same scalar on the base change.
Source: Integral twist paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
def IsPurIntegralTwistComparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (α : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X)
    (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (ρ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (purIntegralTwistAb Y l E) ⟶ purIntegralTwistAb X l E) : Prop :=
  (∀ (V : Y.ProEtᵒᵖ) (b : (purTwistIntegralConstant Y l E).obj.obj V)
      (t : (purTwistZlModule Y l).val.obj V),
    (((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρ).hom.app V
        (purTwistIntegralTensor Y l E V b t) =
      purTwistIntegralTensor X l E ((proEtaleBaseChange h).op.obj V)
        ((proEtaleConstantDirectImageMap h CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app
            V b)
        ((((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) τ).hom.app
          V t)) ∧
  ∀ (V : Y.ProEtᵒᵖ)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj V)
      (t : (purTwistIntegralModule Y l E).val.obj V),
    (((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρ).hom.app V
        (a • t) =
      @id ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        ((proEtaleBaseChange h).op.obj V))
        ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) α).hom.app V a) •
      @id ((purTwistIntegralModule X l E).val.obj ((proEtaleBaseChange h).op.obj V))
        ((((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρ).hom.app V t)

/-- Inverse image of the integral Tate line, including field-inclusion compatibility.
Source: main-20261015 blueprint, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, Roots of unity and Integral twist
(blueprint: lem-pur-integral-twist-line-inverse-image).
Proof:
1. Present each completed coefficient ring as the inverse limit of its finite constant
   quotients (def-weil-completed-integral-coefficients). The integral-limit and pullback
   assertions det-prop-sfb-qlbar-colimit-x-integral-limit and
   det-prop-sfb-qlbar-colimit-x-pullback identify its base change with the same limit on X.
   The finite maps are prop-weil-pbc-proetale-constant-ring-map, so the resulting ring
   comparison is an isomorphism with the stated projections.
2. Apply lem-pur-inverse-image-compatible-free-tower to the finite coefficient/root towers.
   A compatible primitive-root basis on a pro-etale cover is supplied by
   det-def-sp-tate-twist-locally-free; identify slice sites using
   lem-weil-proetale-weakly-etale-localization. The coefficient comparison for Q_l makes
   the ring limit comparison invertible. The maps of roots commute with transitions by
   lem-pur-roots-of-unity-inverse-image-iso and are isomorphisms by
   det-prop-sfb-cartesian-coefficients-twists. Their limit gives tau with its projections.
3. By lem-pe-constant-left-module-inverse-image, constant Z_l and O_H commute with inverse
   image, fixing scalar sections. Apply lem-weil-pbc-ringed-topoi-module-pullback-tensor,
   then tensor tau with the constant O_H comparison. This gives rho and its pure-tensor
   formula. The completed action from lem-pur-twist-sheaf-locally-free is
   (x tensor b)(t tensor a) = xt tensor ba. Check its preservation after every finite
   quotient projection; joint injectivity and local tensor generation give semilinearity.
4. For E into F, the existing integralCompletedScalarMap is fixed by its finite quotient
   maps for sufficiently large source exponents. Both coefficient composites have the
   same projection at every finite level, so are equal. The existing twistScalarMaps at
   one sends t tensor a to t tensor its included coefficient. Both twist composites
   therefore agree on local pure tensors by step 3, and hence agree as sheaf morphisms.
   The construction uses no local generator choices and also applies to empty schemes. -/
theorem pur_integral_twist_line_inverse_image
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (ι : E →ₐ[ℚ_[l]] F) :
    ∃ (αE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
          completedIntegralCommRingSheafUnrestricted l E X)
      (αF : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l F Y) ⟶
          completedIntegralCommRingSheafUnrestricted l F X)
      (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
      (ρE : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        (purIntegralTwistAb Y l E) ⟶ purIntegralTwistAb X l E)
      (ρF : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        (purIntegralTwistAb Y l F) ⟶ purIntegralTwistAb X l F),
      (IsIso αE ∧ IsPurIntegralCoefficientComparison h l E αE) ∧
      (IsIso αF ∧ IsPurIntegralCoefficientComparison h l F αF) ∧
      (IsIso τ ∧ IsPurRootLimitComparison h l τ) ∧
      (IsIso ρE ∧ IsPurIntegralTwistComparison h l E αE τ ρE) ∧
      (IsIso ρF ∧ IsPurIntegralTwistComparison h l F αF τ ρF) ∧
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (integralCompletedScalarMap l E F ι Y) ≫ αF =
        αE ≫ integralCompletedScalarMap l E F ι X ∧
      (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
          (purIntegralTwistScalarMap Y l E F ι) ≫ ρF =
        ρE ≫ purIntegralTwistScalarMap X l E F ι := by
  sorry

end AlgebraicGeometry.Scheme
