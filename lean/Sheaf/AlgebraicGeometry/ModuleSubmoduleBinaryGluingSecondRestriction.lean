/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluingCore
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The second restriction of the binary submodule pullback

Source: Stacks Project, Properties, Lemma 01PF, binary gluing step.
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

set_option maxHeartbeats 600000 in
-- Evaluating the slice-site adjunction requires additional elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- The concrete pullback restricts to Q on V.
Source: Stacks Project, Properties, Lemma 01PF, binary gluing step.
(blueprint: lem-weil-pbc-module-submodule-binary-gluing-second-restriction)
Proof: On an open contained in V the unit is restriction along an isomorphism.
The second projection of its pullback is therefore an isomorphism. Compose it
with the counit, which is also an isomorphism on V, obtaining the stated iso. -/
theorem binarySubmodule_on_V
    (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (ι : Q ⟶ H.over V) :
    Nonempty ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (show V ≤ W ⊔ V from le_sup_right))).obj
          (binarySubmodule X W V H Q ι) ≅ Q) := by
  let R := moduleRings X.toRingedSpace
  let j : V ⟶ W ⊔ V := homOfLE le_sup_right
  let adj := binarySubmoduleAdjunction X W V
  let snd := pullback.snd (adj.unit.app (H.over (W ⊔ V)))
    (binarySubmoduleMap X W V H Q ι)
  let f := (overMap R j).map snd ≫ adj.counit.app Q
  have hc (T : (Over V)ᵒᵖ) : IsIso (f.val.app T) := by
    let A : Over (W ⊔ V) := (Over.map j).obj T.unop
    have hfst : IsIso (pullback.fst A.hom j) := by
      let g : A.left ⟶ CategoryTheory.Limits.pullback A.hom j :=
        pullback.lift (𝟙 _) T.unop.hom (Subsingleton.elim _ _)
      exact ⟨⟨g, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    have hη : IsIso ((adj.unit.app (H.over (W ⊔ V))).val.app (op A)) := by
      apply (ConcreteCategory.isIso_iff_bijective _).2
      have hmap := (H.val.presheaf.map_isIso (pullback.fst A.hom j).op)
      exact (ConcreteCategory.isIso_iff_bijective
        (H.val.presheaf.map (pullback.fst A.hom j).op)).1 hmap
    have hp := (SheafOfModules.evaluation.{u} (R.over (W ⊔ V)) (op A)).map_isPullback
      (IsPullback.of_hasPullback (adj.unit.app (H.over (W ⊔ V)))
        (binarySubmoduleMap X W V H Q ι))
    have hs : IsIso (snd.val.app (op A)) := hp.isIso_snd_of_isIso hη
    have hunit : IsIso ((Over.mapPullbackAdj j).unit.app T.unop) := by
      let g : (Over.pullback j).obj A ⟶ T.unop :=
        Over.homMk (pullback.fst A.hom j) (Subsingleton.elim _ _)
      exact ⟨⟨g, (by ext; apply Subsingleton.elim),
        (by ext; apply Subsingleton.elim)⟩⟩
    have hε : IsIso ((adj.counit.app Q).val.app T) := by
      apply (ConcreteCategory.isIso_iff_bijective _).2
      have hmap := Q.val.presheaf.map_isIso ((Over.mapPullbackAdj j).unit.app T.unop).op
      exact (ConcreteCategory.isIso_iff_bijective
        (Q.val.presheaf.map ((Over.mapPullbackAdj j).unit.app T.unop).op)).1 hmap
    have hs' : IsIso (((overMap R j).map snd).val.app T) := hs
    change IsIso (((overMap R j).map snd).val.app T ≫ (adj.counit.app Q).val.app T)
    infer_instance
  have : IsIso f := isIso_of_components f
  exact ⟨asIso f⟩

end AlgebraicGeometry.Scheme.Modules
