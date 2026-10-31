/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.ScalarProjectionTransformation
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.SectionProjectionUnitSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
set_option maxHeartbeats 800000 in
-- Match the concrete and generic derived tensor comparison instances.
/-- The canonical projection `π_{K,M} : GK ⊗ M ⟶ G(K ⊗ PM)` equals the scalar-first
projection `σ_{M,K}` conjugated by the internal Koszul braidings:
`π_{K,M} = β_{GK,M} ≫ σ_{M,K} ≫ G(β_{PM,K})`.
Source: latest blueprint, sk-thm-sfb-proper-base-change-rational.proof.md, paragraph (3)
(det-thm-sfb-proper-base-change-rational); Stacks Project, Tags 07A4 and 0B56.

Proof: the generic tensor comparison `δ` of `Lf*` used by `scalarFirstProjection` is the
concrete comparison `leftDerivedUpperStarTensor`
(`leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison`), and it commutes with the
Koszul braiding: `Lf*(β_{A,B}) ∘ δ_{B,A} = δ_{A,B} ∘ β_{PA,PB}`
(`leftDerivedUpperStarTensor_braiding`). The internal braiding is the symmetric structure
`DerivedCategory.symmetricCategory'`. The flipped-projection identity
`rightAdjointProjectionMap_flip` for the derived adjunction `P ⊣ G` then gives
`σ_{M,K} = β_{M,GK} ≫ π_{K,M} ≫ G(β_{K,PM})`. Conjugating by `β_{GK,M}` and
`G(β_{PM,K})`, the symmetry `β_{A,B} ≫ β_{B,A} = 𝟙` and functoriality of `G` cancel both
pairs of braidings, leaving `π_{K,M}`. (blueprint: lem-sfb-rational-bivariate-braiding) -/
theorem rational_bivariate_braiding
    (K : DerivedCategory (ModuleObjectRingedComparison.Internal Λ X))
    (M : DerivedCategory (ModuleObjectRingedComparison.Internal Λ Y)) :
    moduleObjectProjectionMap Λ f K M =
      (@BraidedCategory.braiding _ _ _
          (ModuleObjectRingedComparison.internalBraiding Λ Y)
          ((moduleObjectDerivedPushforward Λ f).obj K) M).hom ≫
        (scalarFirstProjection Λ f K).app M ≫
        (moduleObjectDerivedPushforward Λ f).map
          (@BraidedCategory.braiding _ _ _
            (ModuleObjectRingedComparison.internalBraiding Λ X)
            ((moduleObjectDerivedPullback Λ f).obj M) K).hom := by
  let := DerivedCategory.symmetricCategory' (ModuleObjectRingedComparison.Internal Λ X)
  let := DerivedCategory.symmetricCategory' (ModuleObjectRingedComparison.Internal Λ Y)
  have h := CategoryTheory.Adjunction.rightAdjointProjectionMap_flip
    (derivedUpperStarLowerStarAdjunction Λ f) (leftDerivedUpperStarTensor Λ f)
    (leftDerivedUpperStarTensor_braiding Λ f) K M
  dsimp only [scalarFirstProjection]
  rw [← leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]
  rw [h]
  change moduleObjectProjectionMap Λ f K M =
    (β_ ((moduleObjectDerivedPushforward Λ f).obj K) M).hom ≫
      ((β_ M ((moduleObjectDerivedPushforward Λ f).obj K)).hom ≫
        moduleObjectProjectionMap Λ f K M ≫
          (moduleObjectDerivedPushforward Λ f).map
            (β_ K ((moduleObjectDerivedPullback Λ f).obj M)).hom) ≫
      (moduleObjectDerivedPushforward Λ f).map
        (β_ ((moduleObjectDerivedPullback Λ f).obj M) K).hom
  simp only [Category.assoc, SymmetricCategory.symmetry_assoc, ← Functor.map_comp,
    SymmetricCategory.symmetry]
  erw [(moduleObjectDerivedPushforward Λ f).map_id, Category.comp_id]
end AlgebraicGeometry.ProEtale.CondensedRing
