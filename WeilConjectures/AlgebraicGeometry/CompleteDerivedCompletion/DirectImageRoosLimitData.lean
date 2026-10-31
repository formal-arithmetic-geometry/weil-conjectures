/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion
import WeilConjectures.CategoryTheory.DirectImageRoosNormalization.DirectImageRoosNormalization
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization

/-!
# Roos limit data for complete direct images

This is the Milnor cone and product-comparison part of the direct-image limits
proposition.  It is split from the final assembly because it requires the full
normalized Roos calculation.

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proof (1).
(blueprint: prop-weil-pbc-direct-image-limits-roos-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The constant tower evaluated at a level is canonically the identity.
Source: assertion (1), Milnor-cone projections.
(blueprint: prop-weil-pbc-direct-image-limits-roos-data) -/
def constantEvaluationIso (T : Scheme.{u}) (n : ℕ) :
    dconstant l E T ⋙ dev l E T n ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso (constant l E T) (ev l E T n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.constCompEvaluationObj (C := ℕᵒᵖ) (D := AdicCompletion.Modules l E T)
        (Opposite.op n)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Canonical projection from a derived limit to one tower level.
Source: assertion (1), Milnor-cone projections.
(blueprint: prop-weil-pbc-direct-image-limits-roos-data) -/
def levelProjection (T : Scheme.{u}) (n : ℕ) : rlim l E T ⟶ dev l E T n :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (rlim l E T) (constantEvaluationIso l E T n).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (constantLimitAdjunction l E T).counit (dev l E T n) ≫
    (Functor.leftUnitor _).hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Roos triangles, product comparison and the projection compatibility for direct image,
with the levelwise evaluation isomorphisms: assertion (1) of
prop-weil-pbc-direct-image-limits, with its Milnor-cone description.
Source: literature/blueprint/latest/blueprint/sec-proper-base-change/sk-prop-pbc-complete/
prop-weil-pbc-direct-image-limits.proof.md, proof (1); Stacks Tag 0A07.
(blueprint: prop-weil-pbc-direct-image-limits-roos-data)

Proof. The tower direct image is the derived functor of `f_*` applied levelwise, so by
assertions (3) and (4) of det-pbc-complete-derived-completion its evaluation at level `n`
is canonically `Rf_*` of the evaluation at `n`: this is `pushEvaluationMap`, invertible
for every `n`. Products of sheaves of modules on the pro-étale site are exact
(det-pe-products-exact), so both derived categories have countable products, computed
termwise. For a tower `M` the derived limit `rlim M` is the right adjoint of the constant
tower, and its counit at level `n` is `levelProjection`; by def-weil-derived-limit the
derived limit sits in the Milnor (Roos) triangle
`rlim M → ∏ M_n --(1-T)--> ∏ M_n → rlim M[1]` whose first map has components the level
projections. This holds on `X` for `M` and on `Y` for `Rf_*^Tow M`. The product
comparison `Rf_* ∏ M_n → ∏ Rf_* M_n` is invertible because `Rf_*` is a right adjoint, and
it commutes with `1-T` because `T` is a product of transition maps and the comparison is
natural in each factor. Finally `pushLimitIso` is the conjugate of the constant/pullback
comparison, so it is compatible with the counits of the two constant-limit adjunctions;
composing with `pushEvaluationMap` gives the level-projection square. The normalized
direct-image Roos comparison lem-weil-pbc-direct-image-roos-normalization packages the
product, `1-T` and connecting-morphism squares. -/
theorem directImage_roos_limit_data :
    (∀ n : ℕ, IsIso (pushEvaluationMap l E f n)) ∧
    (∃ (_ : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X)))
      (_ : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E Y))),
      ∀ M : DTow l E X,
        (∃ δ, IsDerivedLimitTriangle (fun n : ℕ ↦ (transition l E X n).app M) _
          (Pi.lift fun n : ℕ ↦ (levelProjection l E X n).app M) δ) ∧
        (∃ δ, IsDerivedLimitTriangle
          (fun n : ℕ ↦ (transition l E Y n).app ((rpush l E f).obj M)) _
          (Pi.lift fun n : ℕ ↦ (levelProjection l E Y n).app ((rpush l E f).obj M)) δ) ∧
        IsIso (piComparison (rpushModule l E f) (fun n : ℕ ↦ (dev l E X n).obj M)) ∧
        (rpushModule l E f).map
            (towerTransitionEndomorphism (fun n : ℕ ↦ (transition l E X n).app M)) ≫
            piComparison (rpushModule l E f) (fun n : ℕ ↦ (dev l E X n).obj M) =
          piComparison (rpushModule l E f) (fun n : ℕ ↦ (dev l E X n).obj M) ≫
            towerTransitionEndomorphism
              (fun n : ℕ ↦ (rpushModule l E f).map ((transition l E X n).app M)) ∧
        ∀ n : ℕ, (pushLimitIso l E f).hom.app M ≫
            (levelProjection l E Y n).app ((rpush l E f).obj M) ≫
            (pushEvaluationMap l E f n).app M =
          (rpushModule l E f).map ((levelProjection l E X n).app M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
