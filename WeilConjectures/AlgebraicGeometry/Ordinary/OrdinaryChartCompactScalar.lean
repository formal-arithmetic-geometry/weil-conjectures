/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartRefinementScalar
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Unbounded scalar compatibility of common compactification comparison

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-compactification-scalar).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar

/-- Unbounded scalar compatibility of common compactification comparison.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-compactification-scalar).

Proof: Apply the unbounded refinement scalar square to each projection from the common infimum
compactification.
Expand the canonical common-refinement isomorphism as the first comparison followed by the inverse
second comparison. Cancel the second comparison, apply its scalar square and then the first
square. -/
theorem ordinaryChartCompactificationScalar
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).map
        ((rightDerivedLowerShriekOfCompactificationIso A c d).hom.app M) ≫
      (compactScalarMap φ d).app M =
      (compactScalarMap φ c).app M ≫
        (rightDerivedLowerShriekOfCompactificationIso B c d).hom.app
          ((scalarExtension φ X).obj M) := by
  have h₁ := ordinaryChartRefinementScalar φ (Compactification.infFst c d)
    (Compactification.isPullback_infFst c d) M
  have h₂ := ordinaryChartRefinementScalar φ (Compactification.infSnd c d)
    (Compactification.isPullback_infSnd c d) M
  simp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, asIso_hom]
  apply (cancel_mono ((rightDerivedLowerShriekOfCompactificationComparison
    (ModuleCat.{u + 1} B) (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d)).app
        ((scalarExtension φ X).obj M))).1
  simp only [Category.assoc, asIso_inv, NatIso.isIso_inv_app, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₂]
  simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  exact h₁

end AlgebraicGeometry.Etale
