/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Sheaf.AlgebraicGeometry.NormalizedLocalModulePullback

/-!
# Pullback of finite type locally constant modules

Source: Stacks Project, Modules on Sites, Tag 093R.
(blueprint: lem-sfb-finite-type-constant-module-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

/-- A covering-preserving inverse image which transports constant modules transports
finite type locally constant modules with their unchanged module models.
Source: Stacks Project, Modules on Sites, Tag 093R.
(blueprint: lem-sfb-finite-type-constant-module-pullback). -/
theorem finite_type_constant_module_pullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [PreservesFiniteLimits F]
    (hF : CoverPreserving J K F) (R : Type u) [CommRing R]
    (rho : (constantSheaf J RingCat.{u}).obj (RingCat.of R) ⟶
      (F.sheafPushforwardContinuous RingCat.{u} J K).obj
        ((constantSheaf K RingCat.{u}).obj (RingCat.of R)))
    (c : ∀ M : ModuleCat.{u} R,
      (pullback rho).obj ((strictPerfectConstantSheaf J R).obj M) ≅
        (strictPerfectConstantSheaf K R).obj M)
    (G : SheafOfModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of R)))
    (P : SheafOfModules.{u} ((constantSheaf K RingCat.{u}).obj (RingCat.of R)))
    (b : P ≅ (pullback rho).obj G) (hG : IsFiniteTypeLocallyConstant J R G) :
    IsFiniteTypeLocallyConstant K R P := by
  intro U
  obtain ⟨T, hT, htriv⟩ := hG (⊤_ C)
  let t : U ⟶ F.obj (⊤_ C) := (terminalIsTerminal.isTerminalObj F _).from U
  refine ⟨(T.functorPushforward F).pullback t, K.pullback_stable t
    (hF.cover_preserve hT), ?_⟩
  intro V f hf
  change (T.functorPushforward F) (f ≫ t) at hf
  obtain ⟨W, g, l, hg, hl⟩ := hf
  obtain ⟨M, hM, ⟨e⟩⟩ := htriv W g hg
  obtain ⟨d, _, _⟩ := normalized_local_module_pullback J K F rho _ G _ P (c M) b W e
  refine ⟨M, hM, ⟨?_⟩⟩
  exact ((overFunctorMap _ l).app P).symm ≪≫ (overMap _ l).mapIso d ≪≫
    (overFunctorMap _ l).app ((strictPerfectConstantSheaf K R).obj M)

end SheafOfModules
