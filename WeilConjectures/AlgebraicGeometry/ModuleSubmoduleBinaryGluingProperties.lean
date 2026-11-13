/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleSubmoduleBinaryGluingCore
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.AlgebraicGeometry.ModuleSubmoduleBinaryGluingSecondRestriction

/-! # The restrictions of the binary submodule pullback

## References

* Stacks Project, Properties, Lemma 01PF.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem isIso_of_components
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [∀ T, IsIso (f.val.app T)] : IsIso f := by
  let e := PresheafOfModules.isoMk (fun T ↦ asIso (f.val.app T))
    (fun {_ _} g ↦ f.val.naturality g)
  have : IsIso f.val := by
    change IsIso e.hom
    infer_instance
  have : IsIso ((SheafOfModules.forget R).map f) := ‹IsIso f.val›
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

set_option maxHeartbeats 500000 in
-- Sectionwise pullbacks require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
private theorem binarySubmodule_on_W
    (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (ι : Q ⟶ H.over V)
    [IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ⊓ V ≤ V from inf_le_right))).map ι)] :
    IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ≤ W ⊔ V from le_sup_left))).map
        (binarySubmoduleInclusion X W V H Q ι)) := by
  let R := moduleRings X.toRingedSpace
  let jV : V ⟶ W ⊔ V := homOfLE le_sup_right
  let jW : W ⟶ W ⊔ V := homOfLE le_sup_left
  let f := binarySubmoduleInclusion X W V H Q ι
  have hc (T : (Over W)ᵒᵖ) : IsIso (((overMap R jW).map f).val.app T) := by
    let A : Over (W ⊔ V) := (Over.map jW).obj T.unop
    let B : Over V := (Over.pullback jV).obj A
    have hB : B.left ≤ W ⊓ V :=
      le_inf ((leOfHom (pullback.fst A.hom jV)).trans T.unop.hom.le)
        B.hom.le
    have hι : IsIso (ι.val.app (op B)) := by
      have hi := (SheafOfModules.evaluation.{u} (R.over (W ⊓ V))
        (op (Over.mk (homOfLE hB)))).map_isIso
          ((overMap R (homOfLE (inf_le_right : W ⊓ V ≤ V))).map ι)
      exact hi
    have hm : IsIso ((binarySubmoduleMap X W V H Q ι).val.app (op A)) := by
      dsimp [binarySubmoduleMap, SheafOfModules.overPullback, SheafOfModules.pushforward,
        PresheafOfModules.pushforward, PresheafOfModules.restrictScalars,
        PresheafOfModules.pushforward₀]
      have : IsIso ((ι ≫ (binarySubmoduleRestrictionIso X W V H).inv).val.app (op B)) := by
        change IsIso (ι.val.app (op B) ≫
          (binarySubmoduleRestrictionIso X W V H).inv.val.app (op B))
        have : IsIso ((binarySubmoduleRestrictionIso X W V H).inv.val.app (op B)) :=
          (SheafOfModules.evaluation.{u} _ (op B)).map_isIso
            (binarySubmoduleRestrictionIso X W V H).inv
        infer_instance
      exact (ModuleCat.restrictScalars _).map_isIso
        ((ι ≫ (binarySubmoduleRestrictionIso X W V H).inv).val.app (op B))
    have hp := (SheafOfModules.evaluation.{u} (R.over (W ⊔ V)) (op A)).map_isPullback
      (IsPullback.of_hasPullback
        ((binarySubmoduleAdjunction X W V).unit.app (H.over (W ⊔ V)))
        (binarySubmoduleMap X W V H Q ι))
    exact hp.isIso_fst_of_isIso hm
  exact isIso_of_components ((overMap R jW).map f)

/-- The explicit pullback is the prescribed submodule on `V` and the ambient module on `W`. -/
theorem binarySubmodule_restrictions
    (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (ι : Q ⟶ H.over V)
    [IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ⊓ V ≤ V from inf_le_right))).map ι)] :
    IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ≤ W ⊔ V from le_sup_left))).map
        (binarySubmoduleInclusion X W V H Q ι)) ∧
      Nonempty ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (show V ≤ W ⊔ V from le_sup_right))).obj
          (binarySubmodule X W V H Q ι) ≅ Q)  := by
  exact ⟨binarySubmodule_on_W X W V H Q ι, binarySubmodule_on_V X W V H Q ι⟩

end AlgebraicGeometry.Scheme.Modules
