/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import WeilConjectures.SmoothPurity.CompletedCoefficientNormalization.CompletedCoefficientTensorNormalization
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteTowerLimit
import WeilConjectures.AlgebraicGeometry.Pur.PurRootTowerPreservation
import WeilConjectures.AlgebraicGeometry.Pur.PurIntegralTensorTransport
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement

/-! # Inverse image of the completed integral Tate line

Source: current blueprint, sec-smooth-purity/sk-prop-an,
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

private theorem root_comparison_exists
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        (purTwistZlOne Y l) ⟶ purTwistZlOne X l,
      IsIso τ ∧ IsPurRootLimitComparison h l τ := by
  let L := proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}
  let TY := proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)
  let TX := proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)
  obtain ⟨c, hc⟩ := (proEtaleRootsOfUnityInverseImageIso h).2.1 l (Fact.out : l.Prime)
  have : ∀ j, IsIso (c.app j) := by
    intro j
    rw [hc j.unop]
    exact AlgebraicGeometry.ProEtale.spRoots_cartesian h l (j.unop + 1)
  have : IsIso c := NatIso.isIso_of_isIso_app c
  have : PreservesLimit TY L := pur_root_tower_preservation h l
  let τ := limit.post TY L ≫ lim.map c
  refine ⟨τ, inferInstance, ?_⟩
  intro n
  change (limit.post TY L ≫ limMap c) ≫ limit.π TX (op n) = _
  rw [Category.assoc, limMap_π, limit.post_π_assoc, hc]

end AlgebraicGeometry.Scheme
