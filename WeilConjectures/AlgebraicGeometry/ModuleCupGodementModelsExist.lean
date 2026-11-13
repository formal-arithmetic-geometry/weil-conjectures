/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialExists
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementAugmentation

/-! # Existence of an augmented Godement model -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- A single coefficient sheaf has an augmented concrete Godement model
(Stacks, Tag 0FKR; Banerjee, §1.1.4). -/
theorem moduleCup_godement_models_exist (X : Scheme.{u}) (F : X.Modules) :
    ∃ (A : CosimplicialObject X.Modules)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
        (((alternatingCofaceMapComplex X.Modules).obj A).extend
          ComplexShape.embeddingUpNat)),
      ModuleCupGodementModel X F A a ∧ ModuleCupGodementCodegeneracies X F A := by
  obtain ⟨A, h, hδ, hσ⟩ := moduleCup_godement_cosimplicial_exists X F
  obtain ⟨a, ha⟩ := moduleCup_godement_augmentation_exists X F A h hδ
  exact ⟨A, a, ha, h, hσ⟩

end
end AlgebraicGeometry.Scheme.Modules
