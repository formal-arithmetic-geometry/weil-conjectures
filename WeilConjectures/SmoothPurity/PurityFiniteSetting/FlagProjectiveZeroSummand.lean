/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SmoothPurity.ProjectiveBundleFormula

/-!
# The all-zero summand of the complete flag bundle

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
`thm-pur-localized-top-chern.proof.md`, Step 1
(blueprint: lem-pur-flag-projective-zero-summand).

The projection is characterized on the already published bounded Chern components.
The base-change comparison preserves the actual universal filtration, and the
exchange is the specified adjunction mate followed by coefficient identification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The adjunction unit for a flag projection, through the coefficient identification.
Source: the all-zero component in Step 1 of thm-pur-localized-top-chern.proof.md
(blueprint: lem-pur-flag-projective-zero-summand). -/
def flagCoefficientUnit (P : PurityFiniteSetting.{u})
    {X T : Scheme.{u}} (p : X ⟶ T) :
    P.projectiveBundleUnit T ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) p).rightDerivedFunctor.obj
        (P.projectiveBundleUnit X) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) p).unit.app (P.projectiveBundleUnit T) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) p).rightDerivedFunctor.map
        (P.projectiveBundleUnitPullback p).hom

/-- The all-zero projection is specified by its values on every bounded Chern component.
This is a predicate on a map, with no arbitrary decomposition or splitting as input.
Source: Step 1, iterated projective-bundle formula and its all-zero summand
(blueprint: lem-pur-flag-projective-zero-summand). -/
def IsFlagZeroProjection (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (b : T ⟶ Spec (.of P.field.k))
    (rho : (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (completeFlagBundle r T F).projection).rightDerivedFunctor.obj
        (P.projectiveBundleUnit (completeFlagBundle r T F).scheme) ⟶
          P.projectiveBundleUnit T) : Prop :=
  P.flagCoefficientUnit (completeFlagBundle r T F).projection ≫ rho = 𝟙 _ ∧
    ∀ e : ℕ → ℕ, (∀ j : ℕ, j < r → e j ≤ j) →
      P.flagChernComponent t r T F b e ≫ rho = P.flagZeroComponent T r e

/-- The unit and its canonical all-zero projection are compatible with proper base change.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-localized-top-chern.proof.md, Step 1
(blueprint: lem-pur-flag-projective-zero-summand).

Proof:
1. Induct on r. For r=0 and r=1 the flag projection is the identity and both
   maps are identities. Otherwise use the projectivization and its tautological
   kernel of rank r-1. Tautological geometry makes the projection proper and
   identifies its pullback, including its locally split kernel sequence.
2. Apply the projective-bundle formula at the outer stage and induction on the
   kernel flag. Additivity and the normalized direct-image composition comparison
   give A_T plus the other summands. Projection onto A_T has the stated component
   values; the iterated decomposition makes these values determine it uniquely.
3. The degree-zero components are adjunction units. The composite-adjunction unit
   law and coefficient comparisons identify their iterated inclusion with the unit
   defined above. Successive retraction identities give unit followed by projection
   equal to identity.
4. Pull back every stage and kernel sequence to construct w preserving the universal
   filtration; its square is Cartesian. Proper base change makes the specified
   exchange invertible. Exchange pasting, naturality, the projective-bundle formula's
   base-change clause and induction give the two displayed equations. Uniqueness
   identifies the projections. No purity of a higher-rank bundle is used. -/
theorem flag_projective_zero_summand (P : PurityFiniteSetting.{u})
    (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (b : T ⟶ Spec (.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b] :
    ∃ t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates,
      (∃! rho, P.IsFlagZeroProjection t r T F b rho) ∧
      ∀ (T' : Scheme.{u}) (b' : T' ⟶ Spec (.of P.field.k))
        (_hs : IsSeparated b') (_hft : LocallyOfFiniteType b') (_hqc : QuasiCompact b')
        (g : T' ⟶ T) (_hg : g ≫ b = b') (F' : T'.Modules)
        (_hF' : F'.IsFiniteLocallyFreeOfRank r)
        (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F),
        let := _hF'
        let D := completeFlagBundle r T F
        let D' := completeFlagBundle r T' F'
        ∃ (w : D'.scheme ⟶ D.scheme) (hw : w ≫ D.projection = D'.projection ≫ g),
          IsPullback w D'.projection D.projection g ∧
          (∀ j : ℕ, j ≤ r → ∃ a : (Scheme.Modules.tensorPullback w).obj (D.level j) ≅
              D'.level j,
            (Scheme.Modules.tensorPullback w).map (D.inclusion j) ≫
                (projectiveBundlePullbackComp w D.projection).hom.app F ≫
                (projectiveBundlePullbackCongr hw).hom.app F ≫
                (projectiveBundlePullbackComp D'.projection g).inv.app F ≫
                (Scheme.Modules.tensorPullback D'.projection).map e.inv =
              a.hom ≫ D'.inclusion j) ∧
          let exchange :=
            (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
              (⟨hw⟩ : CommSq w D'.projection D.projection g)).app
                (P.projectiveBundleUnit D.scheme) ≫
              (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
                D'.projection).rightDerivedFunctor.map (P.projectiveBundleUnitPullback w).hom
          IsIso exchange ∧
          (∃! rho', P.IsFlagZeroProjection t r T' F' b' rho') ∧
          (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
              (P.flagCoefficientUnit D.projection) ≫ exchange =
            (P.projectiveBundleUnitPullback g).hom ≫ P.flagCoefficientUnit D'.projection ∧
          ∀ rho rho', P.IsFlagZeroProjection t r T F b rho →
            P.IsFlagZeroProjection t r T' F' b' rho' →
            exchange ≫ rho' =
              (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
                rho ≫ (P.projectiveBundleUnitPullback g).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
