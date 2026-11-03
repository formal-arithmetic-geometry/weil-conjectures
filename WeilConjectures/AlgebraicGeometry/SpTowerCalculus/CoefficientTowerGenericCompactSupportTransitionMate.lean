/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGenericTransitions
public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionData
import WeilConjectures.AlgebraicGeometry.Proper.ProperScalarCounitSquare
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarCounitSquare

/-! # The compact-support scalar counit square

Source: Stacks 07A6, 0D6D, 0D6E and 0D6J
(blueprint: lem-sp-tower-generic-compact-support-counit-square).
The square pastes the proper and open scalar counit squares
(lem-sp-proper-scalar-counit-square, lem-sp-open-scalar-counit-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus
open AlgebraicGeometry.ProEtale.SpShriekTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 2000000 in
-- The derived counit comparisons require a larger elaboration budget.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The compact-support scalar counit square for an arbitrary finite coefficient map.
Source: Stacks 07A6, 0D6D, 0D6E and 0D6J
(blueprint: lem-sp-tower-generic-compact-support-counit-square). -/
private theorem compactSupportScalarCounit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (h : Z ⟶ Y) (H : proEtaleDerivedCategory X B) :
    (scalarExtensionFunctor φ Y).map
        ((intrinsicCompactSupportRestriction φ j h).hom.app H) ≫
      (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := Y) φ)).counit.app
          ((reductionCompactSupport B j h).obj H) =
    (reductionDirectImageComparison φ j h).app ((scalarRestriction φ X).obj H) ≫
      (reductionCompactSupport B j h).map
        ((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := X) φ)).counit.app H) := by
  have hp := ((properScalarCounitSquare φ h).2.2.1
    ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj H)).2
  have ho := congr_app (openScalarCounitSquare φ j) H
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ho
  change (scalarExtensionFunctor φ Y).map
      ((directImageConstantPush A h).map ((sfOpenRestrictionDerived j φ).hom.app H) ≫
        (directImageScalarRestrictionIso φ h).hom.app _) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  erw [hp]
  have hn := (directImageScalarComparison φ h).naturality
    ((sfOpenRestrictionDerived j φ).hom.app H)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← (directImageConstantPush B h).map_comp]
  erw [ho]
  rw [Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- The counit square for finite compact support and intrinsic restriction.
This is the support-side cancellation datum used by the finite proper/open mate
paste; it is the same equation as the second conjunct of
`AlgebraicGeometry.ProEtale.restrictionTransitionTranspose`, here for arbitrary
schemes and with no hypothesis on `H`.
Source: Stacks 07A6, 0D6D, 0D6E and 0D6J
(blueprint: lem-sp-tower-generic-compact-support-counit-square).
Proof: `intrinsicCompactSupportRestriction` is `Rp_*` of the open restriction
comparison followed by the direct-image restriction comparison `D`, and
`reductionDirectImageComparison` is the direct-image scalar comparison `γ` at
`j_!` followed by `Rp_*` of the open tensor comparison. The proper scalar counit
square (lem-sp-proper-scalar-counit-square, third conjunct) rewrites the counit
after `T(D)` as `γ` followed by `Rp_*` of the counit; naturality of `γ` moves it
past the open restriction comparison, and `Rp_*` of the open scalar counit
square (lem-sp-open-scalar-counit-square) gives the right-hand side. -/
theorem generic_compactSupport_counitSquare
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (v : m ≤ n) :
    ∀ H, (scalarExtensionFunctor (quotient l E v) Y).map
        ((intrinsicCompactSupportRestriction (quotient l E v) c.i c.g).hom.app H) ≫
      (proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := Y) (quotient l E v))).counit.app
        ((reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).obj H) =
    (reductionDirectImageComparison (quotient l E v) c.i c.g).app
        ((scalarRestriction (quotient l E v) X).obj H) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        ((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := X) (quotient l E v))).counit.app H) :=
  fun H ↦ compactSupportScalarCounit (quotient l E v) c.i c.g H

end AlgebraicGeometry.ProEtale.SpTowerCalculus
