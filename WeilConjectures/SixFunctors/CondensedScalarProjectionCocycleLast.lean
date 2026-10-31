/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedScalarProjectionCocycleData
import WeilConjectures.SixFunctors.CondensedScalarProjectionCocycleFirst
import WeilConjectures.SixFunctors.CondensedScalarCompactSupportCocycle
import WeilConjectures.SixFunctors.ScalarSix

/-! # Condensed scalar projection cocycle: last boundary block -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem tensorBoundaryTower
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂]
    (T₀₁ : C₀ ⥤ C₁) (T₁₂ : C₁ ⥤ C₂) (T₀₂ : C₀ ⥤ C₂)
    [T₀₁.Monoidal] [T₁₂.Monoidal] [T₀₂.Monoidal]
    (t : T₀₁ ⋙ T₁₂ ⟶ T₀₂) [NatTrans.IsMonoidal t]
    (U₀ V₀ : C₀) (U₁ V₁ : C₁) (U₁₂ V₁₂ U₂ V₂ : C₂)
    (a₀₁ : T₀₁.obj U₀ ⟶ U₁) (b₀₁ : T₀₁.obj V₀ ⟶ V₁)
    (a₁₂ : T₁₂.obj U₁ ⟶ U₁₂) (b₁₂ : T₁₂.obj V₁ ⟶ V₁₂)
    (a₀₂ : T₀₂.obj U₀ ⟶ U₂) (b₀₂ : T₀₂.obj V₀ ⟶ V₂)
    (u : U₁₂ ⟶ U₂) (v : V₁₂ ⟶ V₂)
    (ha : t.app U₀ ≫ a₀₂ = T₁₂.map a₀₁ ≫ a₁₂ ≫ u)
    (hb : t.app V₀ ≫ b₀₂ = T₁₂.map b₀₁ ≫ b₁₂ ≫ v) :
    t.app (U₀ ⊗ V₀) ≫ OplaxMonoidal.δ T₀₂ U₀ V₀ ≫ (a₀₂ ⊗ₘ b₀₂) =
      T₁₂.map (OplaxMonoidal.δ T₀₁ U₀ V₀ ≫ (a₀₁ ⊗ₘ b₀₁)) ≫
        OplaxMonoidal.δ T₁₂ U₁ V₁ ≫ (a₁₂ ⊗ₘ b₁₂) ≫ (u ⊗ₘ v) := by
  rw [reassoc_of% condensedScalarInverseTensorTower T₀₁ T₁₂ T₀₂ t U₀ V₀]
  rw [MonoidalCategory.tensorHom_comp_tensorHom, ha, hb]
  simp only [← MonoidalCategory.tensorHom_comp_tensorHom]
  rw [OplaxMonoidal.δ_natural_assoc]
  simp only [Functor.map_comp, Category.assoc]

set_option maxHeartbeats 10000000 in
-- Normalize several derived-category presentations while keeping their constructions folded.
/-- The source and target boundary cocycles, after normalizing the operation cocycles.

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, successive coefficient changes
(blueprint: lem-sf-condensed-scalar-projection-cocycle-last).

Proof: Expand condensedProjectionScalarSource into the scalar tensor comparison
and the compact-support comparison tensored with an identity. Use the tensor
cocycle and the compact-support cocycle, then interchange tensor products and
composition. Naturality of the tensorator moves the first compact-support
comparison through the second scalar tensorator, yielding the source formula.
For the target expand condensedProjectionScalarTarget and its inner comparison.
Use compact-support naturality to move the inner comparison through the second
compact-support comparison. Apply the tensor and total-derived-pullback
cocycles inside the final compact-support functor, using tensor interchange
and functoriality, to obtain the target formula. The generic tensor calculation
applies directly at the compact-support image, without any additional
preservation hypothesis. These
calculations involve only the two endpoint boundaries: the projection rectangle
itself is proved in the parent directly from the two scalar squares. -/
theorem condensedScalarProjectionCocycleLast
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
(∀ (K : ConstantModelConstructibleFiniteTor Λ₀.X X.left)
      (L : ConstantModelConstructibleFiniteTor Λ₀.X Y.left),
      ((scalarSixTower a b Y.left).hom.app
            ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj K.obj ⊗ L.obj) ≫
          condensedProjectionScalarSource (a ≫ b) c K.obj L.obj =
        (scalarSixChange b Y.left).map (condensedProjectionScalarSource a c K.obj L.obj) ≫
          condensedProjectionScalarSource b c
            ((scalarSixChange a X.left).obj K.obj) ((scalarSixChange a Y.left).obj L.obj) ≫
          ((rightDerivedLowerShriekOfCompactification Λ₂.X c).map
                ((scalarSixTower a b X.left).hom.app K.obj) ▷
              (scalarSixChange b Y.left).obj ((scalarSixChange a Y.left).obj L.obj)) ≫
          ((rightDerivedLowerShriekOfCompactification Λ₂.X c).obj
                ((scalarSixChange (a ≫ b) X.left).obj K.obj) ◁
              (scalarSixTower a b Y.left).hom.app L.obj)) ∧
      ((scalarSixTower a b Y.left).hom.app
            ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj
              (K.obj ⊗ (upperStar Λ₀.X f.left).leftDerivedFunctor.obj L.obj)) ≫
          condensedProjectionScalarTarget (a ≫ b) c K.obj L.obj =
        (scalarSixChange b Y.left).map (condensedProjectionScalarTarget a c K.obj L.obj) ≫
          condensedProjectionScalarTarget b c
            ((scalarSixChange a X.left).obj K.obj) ((scalarSixChange a Y.left).obj L.obj) ≫
          (rightDerivedLowerShriekOfCompactification Λ₂.X c).map
            (((scalarSixTower a b X.left).hom.app K.obj ▷
                (upperStar Λ₂.X f.left).leftDerivedFunctor.obj
                  ((scalarSixChange b Y.left).obj ((scalarSixChange a Y.left).obj L.obj))) ≫
              ((scalarSixChange (a ≫ b) X.left).obj K.obj ◁
                (upperStar Λ₂.X f.left).leftDerivedFunctor.map
                  ((scalarSixTower a b Y.left).hom.app L.obj))))) := by
  classical
  intro K L
  have hfirst := condensedScalarProjectionCocycleFirst ell k _hcd a b _ha _hb f c
  have hq := condensedScalarCompactSupportCocycle ell k _hcd a b _ha _hb f c
  have : NatTrans.IsMonoidal (scalarSixTower a b Y.left).hom :=
    ((scalarSixCoefficientTowerCoherence ell k _hcd a b _ha _hb f).2.2.2.2 Y).1
  have : NatTrans.IsMonoidal (scalarSixTower a b X.left).hom :=
    ((scalarSixCoefficientTowerCoherence ell k _hcd a b _ha _hb f).2.2.2.2 X).1
  refine ⟨?_, ?_⟩
  · simpa only [condensedProjectionScalarSource, scalarSixTensorIso, Iso.symm_hom,
      Monoidal.μIso_inv, MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_id,
      Category.comp_id, Category.assoc] using
      tensorBoundaryTower (scalarSixChange a Y.left) (scalarSixChange b Y.left)
        (scalarSixChange (a ≫ b) Y.left) (scalarSixTower a b Y.left).hom
        ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj K.obj) L.obj
        ((rightDerivedLowerShriekOfCompactification Λ₁.X c).obj
          ((scalarSixChange a X.left).obj K.obj)) ((scalarSixChange a Y.left).obj L.obj)
        ((rightDerivedLowerShriekOfCompactification Λ₂.X c).obj
          ((scalarSixChange b X.left).obj ((scalarSixChange a X.left).obj K.obj)))
        ((scalarSixChange b Y.left).obj ((scalarSixChange a Y.left).obj L.obj))
        ((rightDerivedLowerShriekOfCompactification Λ₂.X c).obj
          ((scalarSixChange (a ≫ b) X.left).obj K.obj))
        ((scalarSixChange (a ≫ b) Y.left).obj L.obj)
        ((scalarCompactSupportMap a c.i c.g).app K.obj) (𝟙 _)
        ((scalarCompactSupportMap b c.i c.g).app ((scalarSixChange a X.left).obj K.obj))
        (𝟙 _) ((scalarCompactSupportMap (a ≫ b) c.i c.g).app K.obj) (𝟙 _)
        ((rightDerivedLowerShriekOfCompactification Λ₂.X c).map
          ((scalarSixTower a b X.left).hom.app K.obj))
        ((scalarSixTower a b Y.left).hom.app L.obj) (hq K.obj)
        (by
          simp only [Category.comp_id, Category.id_comp]
          rw [(scalarSixChange b Y.left).map_id, Category.id_comp])
  · have hd : (scalarSixTower a b X.left).hom.app
          (K.obj ⊗ (upperStar Λ₀.X f.left).leftDerivedFunctor.obj L.obj) ≫
          condensedProjectionScalarInner (a ≫ b) f.left K.obj L.obj =
        (scalarSixChange b X.left).map
            (condensedProjectionScalarInner a f.left K.obj L.obj) ≫
          condensedProjectionScalarInner b f.left
            ((scalarSixChange a X.left).obj K.obj) ((scalarSixChange a Y.left).obj L.obj) ≫
          (((scalarSixTower a b X.left).hom.app K.obj ▷
              (upperStar Λ₂.X f.left).leftDerivedFunctor.obj
                ((scalarSixChange b Y.left).obj ((scalarSixChange a Y.left).obj L.obj))) ≫
            ((scalarSixChange (a ≫ b) X.left).obj K.obj ◁
              (upperStar Λ₂.X f.left).leftDerivedFunctor.map
                ((scalarSixTower a b Y.left).hom.app L.obj))) := by
      simpa only [condensedProjectionScalarInner, scalarSixTensorIso, Iso.symm_hom,
        Monoidal.μIso_inv, MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight,
        Category.id_comp, Category.assoc] using
        tensorBoundaryTower (scalarSixChange a X.left) (scalarSixChange b X.left)
          (scalarSixChange (a ≫ b) X.left) (scalarSixTower a b X.left).hom
          K.obj ((upperStar Λ₀.X f.left).leftDerivedFunctor.obj L.obj)
          ((scalarSixChange a X.left).obj K.obj)
          ((upperStar Λ₁.X f.left).leftDerivedFunctor.obj
            ((scalarSixChange a Y.left).obj L.obj))
          ((scalarSixChange b X.left).obj ((scalarSixChange a X.left).obj K.obj))
          ((upperStar Λ₂.X f.left).leftDerivedFunctor.obj
            ((scalarSixChange b Y.left).obj ((scalarSixChange a Y.left).obj L.obj)))
          ((scalarSixChange (a ≫ b) X.left).obj K.obj)
          ((upperStar Λ₂.X f.left).leftDerivedFunctor.obj
            ((scalarSixChange (a ≫ b) Y.left).obj L.obj))
          (𝟙 _) ((condensedScalarPullbackIso a f.left).hom.app L.obj)
          (𝟙 _) ((condensedScalarPullbackIso b f.left).hom.app
            ((scalarSixChange a Y.left).obj L.obj))
          (𝟙 _) ((condensedScalarPullbackIso (a ≫ b) f.left).hom.app L.obj)
          ((scalarSixTower a b X.left).hom.app K.obj)
          ((upperStar Λ₂.X f.left).leftDerivedFunctor.map
            ((scalarSixTower a b Y.left).hom.app L.obj))
          (by
            simp only [Category.comp_id, Category.id_comp]
            rw [(scalarSixChange b X.left).map_id, Category.id_comp])
          (hfirst.2.1 L)
    have hn := (scalarCompactSupportMap b c.i c.g).naturality
      (condensedProjectionScalarInner a f.left K.obj L.obj)
    simp only [Functor.comp_map] at hn
    simp only [condensedProjectionScalarTarget, Category.assoc]
    erw [reassoc_of% hq (K.obj ⊗ (upperStar Λ₀.X f.left).leftDerivedFunctor.obj L.obj)]
    erw [← (rightDerivedLowerShriekOfCompactification Λ₂.X c).map_comp, hd]
    simp only [Functor.map_comp, Category.assoc]
    erw [← reassoc_of% hn]
    all_goals rfl

end AlgebraicGeometry.ProEtale.CondensedRing
