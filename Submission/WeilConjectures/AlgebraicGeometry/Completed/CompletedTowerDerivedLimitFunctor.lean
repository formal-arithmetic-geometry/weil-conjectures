/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The functorial completed-coefficient derived inverse limit

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1242;
Stacks Tags 08TC, 079P and 0BK7 (blueprint: prop-weil-pbc-rlim-functoriality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Strict module towers have K-injective resolutions in the unrestricted module category.
Source: Stacks Tags 079B and 079Q (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: the strict tower category is Grothendieck abelian by the adic datum's diagram
category theorem after small-site transport. Grothendieck abelian categories have
K-injective resolutions. Transport back preserves quasi-isomorphisms and homotopies. -/
@[instance]
theorem completedTowers_hasKInjectiveResolutions (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    Abelian.HasKInjectiveResolutions (pbcTowers T R) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  have : IsGrothendieckAbelian.{u + 1} (pbcTowers T R) :=
    reductionTower_isGrothendieckAbelian T ((adicLisseForget T).obj R)
  infer_instance

/-- The limit functor on strict module towers is additive.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: a map between limits is determined by its composites with the projections.
Both addition and the limit maps have their specified component maps, giving the equality. -/
@[instance]
theorem completedTowerLimit_additive (T : Scheme.{u}) :
    (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
      pbcModules T (pbcAdicCompletion T d)).Additive := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  exact Functor.additive_of_preserves_binary_products _

/-- Constant strict towers, with all transitions equal to the identity.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedTowerConstant (T : Scheme.{u}) :=
  (Functor.const ℕᵒᵖ : pbcModules T (pbcAdicCompletion T d) ⥤
    pbcTowers T (pbcAdicCompletion T d))

/-- Constant towers are additive and exact, since tower exactness is levelwise.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: all evaluations of the constant functor are the identity functor. Kernels,
cokernels and addition are computed at each level, proving the three assertions. -/
theorem completedTowerConstant_exact (T : Scheme.{u}) :
    (completedTowerConstant d T).Additive ∧
    PreservesFiniteLimits (completedTowerConstant d T) ∧
    PreservesFiniteColimits (completedTowerConstant d T) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Additivity of the specified constant tower functor.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance completedTowerConstant_additive (T : Scheme.{u}) :
    (completedTowerConstant d T).Additive := (completedTowerConstant_exact d T).1

/-- Exactness on kernels for constant towers.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance completedTowerConstant_finiteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (completedTowerConstant d T) :=
  (completedTowerConstant_exact d T).2.1

/-- Exactness on cokernels for constant towers.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance completedTowerConstant_finiteColimits (T : Scheme.{u}) :
    PreservesFiniteColimits (completedTowerConstant d T) :=
  (completedTowerConstant_exact d T).2.2

/-- Constant towers on derived objects by exact termwise descent.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedDerivedConstant (T : Scheme.{u}) :=
  (completedTowerConstant d T).mapDerivedCategory

end AlgebraicGeometry.Scheme
