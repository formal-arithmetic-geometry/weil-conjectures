/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedProjectionScalarSquare
import WeilConjectures.SixFunctors.CondensedScalarProjectionCocycleData
import WeilConjectures.SixFunctors.ScalarSix
import WeilConjectures.SixFunctors.CondensedScalarCompactSupportCocycle

/-! # Condensed scalar projection cocycle: first boundary block -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u u₀ u₁ u₂ v₀ v₁ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 3000000 in
-- Normalize several derived-category presentations while keeping their constructions folded.
/-- The tensor, total-derived-pullback and compact-support scalar
cocycles, before the projection morphism is inserted.

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, successive coefficient changes
(blueprint: lem-sf-condensed-scalar-projection-cocycle-first).

Proof: For the tensor identity apply monoidality of the scalar tower in
scalarSixCoefficientTowerCoherence. Precompose its tensorator equation by the
inverse tensorator of the composite functor and postcompose by the inverse
scalar tensorator; expand the composite tensorator to obtain the displayed
inverse-tensorator formula. For pullback start with ScalarSixPullbackData.tower.
Whisker with the exact-to-total-derived pullback isomorphisms defining
condensedScalarPullbackIso. Naturality of scalarSixTower cancels the initial
presentation comparison, and naturality of the final presentation comparison
cancels its other end. For compact support expand scalarCompactSupportMap as
the direct-image mate followed by direct image of the open scalar comparison.
Use scalarDirectImageMateCoherence at the open extension of K. Move the open
comparison through the second direct-image mate by naturality, then apply the
coefficient-tower equation for the normalized open comparison. This equation
is obtained from the normalized immersion tower and its openComparison
identification; cancel the three open-presentation isomorphisms. Mapping the
result under direct image gives the compact-support equation for the supplied
compactification c. No canonical choice of c is used. -/
theorem condensedScalarProjectionCocycleFirst
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}}
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂)
    (_ha : ListedCoefficientMap ell a) (_hb : ListedCoefficientMap ell b)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left) :
(∀ (Z : Over (Spec (.of k)))
      [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
      (U V : ConstantModelConstructibleFiniteTor Λ₀.X Z.left),
      (scalarSixTower a b Z.left).hom.app (U.obj ⊗ V.obj) ≫
          (scalarSixTensorIso (a ≫ b) Z.left U.obj V.obj).hom =
        (scalarSixChange b Z.left).map ((scalarSixTensorIso a Z.left U.obj V.obj).hom) ≫
          (scalarSixTensorIso b Z.left
              ((scalarSixChange a Z.left).obj U.obj)
              ((scalarSixChange a Z.left).obj V.obj)).hom ≫
          ((scalarSixTower a b Z.left).hom.app U.obj ▷
              (scalarSixChange b Z.left).obj ((scalarSixChange a Z.left).obj V.obj)) ≫
          ((scalarSixChange (a ≫ b) Z.left).obj U.obj ◁
              (scalarSixTower a b Z.left).hom.app V.obj)) ∧
    (∀ L : ConstantModelConstructibleFiniteTor Λ₀.X Y.left,
      (scalarSixTower a b X.left).hom.app
            ((upperStar Λ₀.X f.left).leftDerivedFunctor.obj L.obj) ≫
          (condensedScalarPullbackIso (a ≫ b) f.left).hom.app L.obj =
        (scalarSixChange b X.left).map
            ((condensedScalarPullbackIso a f.left).hom.app L.obj) ≫
          (condensedScalarPullbackIso b f.left).hom.app
            ((scalarSixChange a Y.left).obj L.obj) ≫
          (upperStar Λ₂.X f.left).leftDerivedFunctor.map
            ((scalarSixTower a b Y.left).hom.app L.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ₀.X X.left,
      (scalarSixTower a b Y.left).hom.app
            ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj K.obj) ≫
          (scalarCompactSupportMap (a ≫ b) c.i c.g).app K.obj =
        (scalarSixChange b Y.left).map ((scalarCompactSupportMap a c.i c.g).app K.obj) ≫
          (scalarCompactSupportMap b c.i c.g).app ((scalarSixChange a X.left).obj K.obj) ≫
          (rightDerivedLowerShriekOfCompactification Λ₂.X c).map
            ((scalarSixTower a b X.left).hom.app K.obj)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro Z _ _ _ U V
    have : NatTrans.IsMonoidal (scalarSixTower a b Z.left).hom :=
      ((scalarSixCoefficientTowerCoherence ell k _hcd a b _ha _hb f).2.2.2.2 Z).1
    simpa only [scalarSixTensorIso, Iso.symm_hom, Monoidal.μIso_inv,
      MonoidalCategory.tensorHom_def, Category.assoc] using
      condensedScalarInverseTensorTower (scalarSixChange a Z.left) (scalarSixChange b Z.left)
        (scalarSixChange (a ≫ b) Z.left) (scalarSixTower a b Z.left).hom U.obj V.obj
  · intro L
    exact condensedScalarCocyclePresentationTransport
      (scalarSixChange a Y.left) (scalarSixChange b Y.left)
      (scalarSixChange (a ≫ b) Y.left)
      (scalarSixChange a X.left) (scalarSixChange b X.left)
      (scalarSixChange (a ≫ b) X.left)
      (scalarSixPull Λ₀ f.left) (upperStar Λ₀.X f.left).leftDerivedFunctor
      (scalarSixPull Λ₁ f.left) (upperStar Λ₁.X f.left).leftDerivedFunctor
      (scalarSixPull Λ₂ f.left) (upperStar Λ₂.X f.left).leftDerivedFunctor
      (leftDerivedUpperStarIsoMapDerivedCategory Λ₀.X f.left)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ₁.X f.left)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ₂.X f.left)
      (scalarDirectImagePullbackData.theta a f.left)
      (scalarDirectImagePullbackData.theta b f.left)
      (scalarDirectImagePullbackData.theta (a ≫ b) f.left)
      (scalarSixTower a b Y.left) (scalarSixTower a b X.left)
      (scalarDirectImagePullbackData.tower a b f.left) L.obj
  · intro K
    exact condensedScalarCompactSupportCocycle ell k _hcd a b _ha _hb f c K.obj

end AlgebraicGeometry.ProEtale.CondensedRing
