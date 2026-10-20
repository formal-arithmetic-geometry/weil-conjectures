/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import Sheaf.AlgebraicGeometry.ModuleCechComparison

/-! # Cech comparison data for acyclic module resolutions

Source: Stacks Project, Tags 01EQ and 0FKV.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The first-quadrant Cech double complex of an arbitrary module complex,
with resolution degree first. This extends moduleCechDouble to acyclic resolutions.
Source: Stacks Project, Tag 01EQ.
(blueprint: def-sc-cech-cup-resolution-comparison-data) -/
def cupCechDouble {X : Scheme.{v}} {ι : Type v} (U : ι → X.Opens)
    (K : CochainComplex X.Modules ℕ) :
    HomologicalComplex₂ (ModuleCat.{v} Γ(X, ⊤)) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- Alpha, beta and the computing identification for an acyclic resolution.
The component equations specify the actual restriction and augmentation maps.
The class equations identify them with the canonical injective comparisons.
Source: Stacks Project, Tags 01EQ and 0FKV.
(blueprint: def-sc-cech-cup-resolution-comparison-data) -/
structure CupCechResolutionComparison {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} (D : CupAcyclicResolution F) where
  alpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj D.K ⟶ (cupCechDouble U D.K).total (ComplexShape.up ℕ)
  beta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
    (cupCechDouble U D.K).total (ComplexShape.up ℕ)
  alpha_f : ∀ n : ℕ, alpha.f n = moduleCechZero U (D.K.X n) ≫
    (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp)
  beta_f : ∀ n : ℕ, beta.f n =
    ((cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (D.augmentation.f 0).val)).f n ≫
      (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)
  alpha_quasiIso : QuasiIso alpha
  iso : ∀ n : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace n).obj F ≅
    ((cupCechDouble U D.K).total (ComplexShape.up ℕ)).homology n
  alpha_class : ∀ (n : ℕ)
    (z : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K),
    (iso n).hom (D.class n z) =
      HomologicalComplex.homologyMap alpha n (cupCycleClass _ n z)
  beta_class : ∀ (n : ℕ)
    (c : ((cechComplexFunctor U).obj F.presheafModuleCat).homology n ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace n).obj F),
    IsModuleCechComparison U F n c →
    ∀ z : (((cechComplexFunctor U).obj F.presheafModuleCat).sc n).moduleCatLeftHomologyData.K,
      (iso n).hom (c (cupCycleClass _ n z)) =
        HomologicalComplex.homologyMap beta n (cupCycleClass _ n z)

end
end AlgebraicGeometry.Scheme.Modules
