/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import all WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleMapFrameCoordinates
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseChangeCoordinates
import all WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import all WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefixBaseChange
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
import all WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence

/-! # Exchange of vector-bundle chart source comparisons

Source: blueprint latest, sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2; local swap proof, Steps 1--2.
(blueprint: lem-pur-vector-integration-swap-chart-prefix).
-/

@[expose] public noncomputable section
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open VectorBundleZeroSection
attribute [local irreducible] _root_.DerivedCategory.singleFunctors
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom Matrix
  vectorIntegrationCoefficient vectorIntegrationSource
attribute [local irreducible] rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor
private lemma named_compositor
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (r : X ⟶ Y) (v : Y ⟶ Z) (k : X ⟶ Z) (e : k = r ≫ v) :
    eqToIso (congrArg (ordinaryFinitePullback A) e) ≪≫
        leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v k e := by
  subst k
  simp only [eqToIso_refl, Iso.refl_trans]

private lemma square_iso_calculation
    {C D : Type*} [Category C] [Category D] {F G H K : C ⥤ D}
    (a : F ≅ K) (b : G ≅ H) (c : F ≅ H) (e : F = G)
    (h : eqToIso e ≪≫ b = c) :
    a.symm ≪≫ eqToIso e ≪≫ b = (c.symm ≪≫ a).symm := by
  rw [h, Iso.trans_symm, Iso.symm_symm_eq]

private lemma inverse_square_comparison
    (A : Type (u + 1)) [CommRing A] {X X' Y Y' : Scheme.{u}}
    (q : X' ⟶ X) (r : X' ⟶ Y') (p : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : CommSq q r p v) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).symm ≪≫
      eqToIso (congrArg (ordinaryFinitePullback A) sq.w) ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm := by
  delta derivedSquareUpperStarIso
  exact square_iso_calculation
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v (q ≫ p) sq.w)
    (congrArg (ordinaryFinitePullback A) sq.w)
    (named_compositor A r v (q ≫ p) sq.w)

end AlgebraicGeometry.Etale
