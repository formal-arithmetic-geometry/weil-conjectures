/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Skyscraper sheaves and the closure of a point

Source: Stacks Project, Modules, proof of Tag 0CAL; Sheaves, Definition Tag 009A.
(blueprint: lem-weil-pbc-skyscraper-constant-on-point-closure).
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat

open Classical in
/-- Source: Stacks Project, Modules, proof of Tag 0CAL; Sheaves, Definition Tag 009A.
(blueprint: lem-weil-pbc-skyscraper-constant-on-point-closure).
The sheaf `F`, with the section identifications `e` commuting with restrictions, is precisely
the direct image from the closure of `y` of the sheaf of locally constant maps into `A`.
The isomorphism `kappa` sends a section `a` on an open containing `y` to the constant map
with value `a`. On any other open its image is the unique map on the empty intersection.

Proof (the five elementary steps of the node, expanding the claim omitted in Tag 0CAL):
1. An open meeting the closure of `{y}` contains `y`: every neighbourhood of a point of
   that closure meets `{y}`. Conversely `y` itself witnesses the intersection.
2. A locally constant map is constant near each point of the intersection. That
   neighbourhood also contains `y` by step 1, so every value equals its value at `y`.
3. On an open containing `y`, evaluation at `y` inverts the constant-map assignment.
   Otherwise the intersection is empty and both section sets have exactly one element.
4. These assignments commute with restrictions: either the smaller open contains `y`
   and constant maps restrict to constant maps, or its intersection is empty and both
   resulting maps are the empty map. The impossible fourth case is excluded by inclusion.
5. Locally constant maps glue uniquely over open covers, and the glued map remains
   locally constant. Thus they give a sheaf. The sectionwise bijections from step 3 and
   naturality from step 4 give an isomorphism of sheaves, with natural inverse bijections. -/
theorem skyscraper_constant_on_point_closure (Y : TopCat.{u}) (y : Y) (A : Type u) :
    (∀ V : Opens Y, ((V : Set Y) ∩ closure ({y} : Set Y)).Nonempty ↔ y ∈ V) ∧
    (∀ (V : Opens Y), y ∈ V →
      ∀ g : LocallyConstant {w : Y // w ∈ V ∧ w ∈ closure ({y} : Set Y)} A,
        ∃ a : A, ∀ w, g w = a) ∧
    ∃ (F : Y.Sheaf (Type u))
      (e : ∀ V : Opens Y,
        F.obj.obj (op V) ≃
          LocallyConstant {w : Y // w ∈ V ∧ w ∈ closure ({y} : Set Y)} A),
      (∀ (U V : Opens Y) (i : U ⟶ V) (s : F.obj.obj (op V)),
        e U (F.obj.map i.op s) = LocallyConstant.comap
          ⟨fun w : {w : Y // w ∈ U ∧ w ∈ closure ({y} : Set Y)} ↦
            ⟨w.1, i.le w.2.1, w.2.2⟩,
            continuous_subtype_val.subtype_mk _⟩ (e V s)) ∧
      ∃ kappa : skyscraperSheaf y A ≅ F,
        (∀ V : Opens Y, Function.Bijective (kappa.hom.hom.app (op V))) ∧
        (∀ (V : Opens Y) (hy : y ∈ V) (a : A),
          e V (kappa.hom.hom.app (op V) (cast (if_pos hy).symm a)) =
            LocallyConstant.const _ a) ∧
        (∀ (V : Opens Y), y ∉ V →
          ∀ (s : (skyscraperSheaf y A).obj.obj (op V))
            (g : LocallyConstant {w : Y // w ∈ V ∧ w ∈ closure ({y} : Set Y)} A),
            e V (kappa.hom.hom.app (op V) s) = g) := by
  sorry

end TopCat
