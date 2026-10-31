/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBaseChangeCalculus
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

/-! # Normalized mates at finite coefficients, before substituting bundle schemes. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

/-- Scalar trace compatibility determines the exceptional base-change mate at finite coefficients.
Source: current blueprint sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2.
Proof: specialize the proved projection/normalization/mate calculation. The projection formula
and compact-support exchange are invertible at finite coefficients. Supply the published raw
projection-exchange equation. The inverse pullback-square comparison is the definition of
purityPullbackSquare, and the exceptional exchange is defined as the mate of inverse compact
exchange. No geometric trace statement is used in this specialization.
(blueprint: lem-pur-finite-normalized-base-change). -/
theorem finiteIntegrationNormalized_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (W : Etale.DerivedCategoryModule A X) (W' : Etale.DerivedCategoryModule A X')
    (l : (RfPullback A g').obj W ≅ W')
    (t : (RfShriek A f).obj W ⟶ 𝟙_ _) (t' : (RfShriek A f').obj W' ⟶ 𝟙_ _)
    (a : ∀ K : Etale.DerivedCategoryModule A Y,
      (RfPullback A g').obj (W ⊗ (RfPullback A f).obj K) ≅
        W' ⊗ (RfPullback A f').obj ((RfPullback A g).obj K))
    (ha : ∀ K : Etale.DerivedCategoryModule A Y,
      HEq ((Etale.leftDerivedUpperStarTensorIso (ModuleCat A) g' W
        ((RfPullback A f).obj K) ≪≫ (l ⊗ᵢ purityPullbackSquare A sq K)).hom)
        (a K).hom)
    (γ : RfPullback A f ⋙ tensorLeft W ⟶ RfUpper A f)
    (γ' : RfPullback A f' ⋙ tensorLeft W' ⟶ RfUpper A f')
    (hn : IntegrationGammaNormalized (RfShriek A f) (RfUpper A f) (RfPullback A f)
      (Etale.rightDerivedUpperShriekAdjunction A f)
      W t ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W) γ)
    (hn' : IntegrationGammaNormalized (RfShriek A f') (RfUpper A f') (RfPullback A f')
      (Etale.rightDerivedUpperShriekAdjunction A f')
      W' t' ((Etale.projectionMap (ModuleCat.{u + 1} A) f').app W') γ')
    (hi : ∀ K, IsIso (γ.app K)) (hi' : ∀ K, IsIso (γ'.app K))
    (ht : (Etale.rightDerivedLowerShriekBaseChangeMap A sq).app W ≫
      (RfShriek A f').map l.hom ≫ t' =
      (RfPullback A g).map t ≫ (Etale.leftDerivedUpperStarUnitIso (ModuleCat A) g).hom)
    (K : Etale.DerivedCategoryModule A Y) :
    IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K) ∧
      (RfPullback A g').map (γ.app K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K =
      (a K).hom ≫ γ'.app ((RfPullback A g).obj K) := by
  let := Etale.isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let : IsIso (Etale.projectionMap (ModuleCat.{u + 1} A) f) :=
    Etale.isIso_projectionMap_of_finite A f
  let b : RfShriek A f ⋙ RfPullback A g ≅ RfPullback A g' ⋙ RfShriek A f' :=
    { hom := Etale.rightDerivedLowerShriekBaseChangeMap A sq
      inv := inv (Etale.rightDerivedLowerShriekBaseChangeMap A sq)
      hom_inv_id := IsIso.hom_inv_id _
      inv_hom_id := IsIso.inv_hom_id _ }
  have h := integrationNormalized_baseChange_calculus (ModuleCat.{u + 1} A) sq
    (Etale.projectionMap (ModuleCat.{u + 1} A) f)
    (Etale.projectionMap (ModuleCat.{u + 1} A) f') (RfUpper A f) (RfUpper A f')
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction A f')
    b W W' l t t' γ γ' hn hn' hi hi' ht
    (fun M ↦ Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap A sq W M) K
  refine ⟨h.1, ?_⟩
  calc
    _ = (Etale.leftDerivedUpperStarTensorIso (ModuleCat A) g' W
        ((RfPullback A f).obj K) ≪≫ (l ⊗ᵢ purityPullbackSquare A sq K)).hom ≫
        γ'.app ((RfPullback A g).obj K) := h.2
    _ = _ := congrArg (fun m ↦ m ≫ γ'.app ((RfPullback A g).obj K)) (eq_of_heq (ha K))

end WeilConjectures.PurityFiniteSetting
