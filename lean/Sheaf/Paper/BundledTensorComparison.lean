/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearSystemModels

/-! # Bundled representative-normalized tensor comparisons

Source: Stacks 03EL and 07A4.
(blueprint: def-sf-bundled-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.SemilinearSections

/-- A tensor comparison together with its ordinary and total-complex model.
Source: Stacks 03EL and 07A4 (blueprint: def-sf-bundled-tensor-comparison). -/
structure BundledTensorComparison {C D : Type c} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf K CommRingCat.{max c v r})
    (F : Mod.{c, v, max c v r} J R ⥤ Mod.{c, v, max c v r} K S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (A : Closed.{c, v, r} J R) (B : Closed.{c, v, r} K S)
    (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} K S B) where
  /-- The derived comparison. -/
  mu : A.tensor ⋙ F.mapDerivedCategory ≅
    (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor
  /-- Its ordinary and chain model. -/
  model : TensorComparisonModel.{c, v, r} J K R S F A B TA TB mu

end WeilConjectures.SemilinearSections
