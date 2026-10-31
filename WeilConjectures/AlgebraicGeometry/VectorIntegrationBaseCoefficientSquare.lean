/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.VectorBundleIntegrationCharts
import WeilConjectures.AlgebraicGeometry.VectorIntegrationBaseCoefficientComposition
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
/-! # Normalized coefficient pullback around a commutative square

Source: vector-bundle purity proof, paragraph 2, coefficient transport.
(blueprint: lem-pur-vector-integration-base-coefficient-square).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] upperStar Functor.leftDerivedFunctor
  Functor.mapDerivedCategory leftDerivedUpperStarComp
attribute [local implicit_reducible] ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor
/-- Normalized Tate-coefficient pullback is compatible with a commutative square.
Source: blueprint vector-bundle purity proof, paragraph 2, coefficient transport.
(blueprint: lem-pur-vector-integration-base-coefficient-square).

Proof: Apply vectorIntegrationBaseCoefficientPullback_comp to both paths, choosing g′ ≫ f as
common composite. The commutativity equality supplies the other path. Both resulting composites
are the normalized pullback along that common map. Precompose the claimed equality by the
invertible compositor for the first path. Expand derivedSquareUpperStarIso: its inverse consists
of the inverse compositor for the first path followed by the compositor for the second. Cancel
the first compositor with its inverse; the claim is exactly the second path equation followed by
the inverse of the first path equation. No Cartesian hypothesis is needed. The argument includes
zero powers, empty schemes and the zero ring, and allows independent intermediate unit proofs.
-/
theorem vectorIntegrationBaseCoefficientPullback_square
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
    (hY' : IsUnit (N : Γ(Y', ⊤))) (d : ℕ) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app
        (affineLinearBaseCoefficient A N hA Y d) ≫
      (ordinaryFinitePullback A f').map
        (vectorIntegrationBaseCoefficientPullback A N hA t g hY d).hom ≫
      (vectorIntegrationBaseCoefficientPullback A N hA t f' hY' d).hom =
    (ordinaryFinitePullback A g').map
        (vectorIntegrationBaseCoefficientPullback A N hA t f hY d).hom ≫
      (vectorIntegrationBaseCoefficientPullback A N hA t g' hX d).hom := by
  have hp := vectorIntegrationBaseCoefficientPullback_comp A N hA t g' f
    (g' ≫ f) rfl hY hX d
  have hf := vectorIntegrationBaseCoefficientPullback_comp A N hA t f' g
    (g' ≫ f) sq.w hY hY' d
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g' f).hom.app
    (affineLinearBaseCoefficient A N hA Y d))).mp
  simp only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact hf.trans hp.symm
end AlgebraicGeometry.Etale
