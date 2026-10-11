/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Evaluation of germs of locally constant maps

Source: Stacks Project, Sheaves on Spaces, Definition 6.7.4 (Tag 006W) and
Example 6.11.3 (Tag 007B) (blueprint: lem-weil-pbc-locally-constant-germ-evaluation).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat

/-- Evaluation identifies the germs of locally constant maps with the coefficient set.
Source: Stacks Project, Tags 006W and 007B
(blueprint: lem-weil-pbc-locally-constant-germ-evaluation).

The presheaf `L` below is exactly `V ↦ L_R(V)`, the locally constant maps `V → R`, with
restriction of maps (written inline as in lem-weil-pbc-closed-pushforward-constant-restriction).
Its stalk `L.stalk x` is by definition the colimit [def-weil-pbc-category-colimit] of `L`
over the open neighbourhoods of `x` ordered by reverse inclusion, and `L.germ V x hx` is the
coprojection `g ↦ g_x`.

Proof: Evaluation at `x` commutes with restriction, so the colimit universal property
[def-weil-pbc-category-colimit] gives a unique map with the displayed value on each germ.
Every colimit element is represented by a section
[lem-weil-pbc-filtered-colimit-sets-elementwise]. For surjectivity, the constant section with
value `r` has a germ evaluating to `r`. For injectivity, representatives with the same value
at `x` are constant on respective open neighbourhoods of `x`. Their restrictions to the
intersection agree, so their germs agree by the eventual-equality criterion for filtered
colimits [lem-weil-pbc-filtered-colimit-sets-elementwise]. -/
theorem existsUnique_locallyConstant_germ_evaluation (X : TopCat.{u}) (x : X) (R : Type u) :
    let L : X.Presheaf (Type u) :=
      { obj := fun V ↦ LocallyConstant {y : X // y ∈ unop V} R
        map := fun {U V} i ↦ TypeCat.ofHom (LocallyConstant.comap
          ⟨fun y : {y : X // y ∈ unop V} ↦ ⟨y.1, i.unop.le y.2⟩,
            continuous_subtype_val.subtype_mk _⟩)
        map_id := by intros; rfl
        map_comp := by intros; rfl }
    ∃ ev : L.stalk x → R,
      (∀ (V : Opens X) (hx : x ∈ V) (g : LocallyConstant V R),
        ev (L.germ V x hx g) = g ⟨x, hx⟩) ∧
      Function.Bijective ev ∧
      ∀ ev' : L.stalk x → R,
        (∀ (V : Opens X) (hx : x ∈ V) (g : LocallyConstant V R),
          ev' (L.germ V x hx g) = g ⟨x, hx⟩) → ev' = ev := by
  sorry

end TopCat
