/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Topology.SetsExtensionByEmpty
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Bases
import Sheaf.Topology.SetsExtensionByEmptyAdjunction

/-!
# Covering a sheaf of sets by constant sheaves on basis opens

Source: Stacks Project, Modules, Lemma 17.19.1 (Tag 0CAH)
(blueprint: lem-weil-pbc-sheaf-basis-surjection).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Every sheaf of sets is the target of an epimorphism from a coproduct of extensions by
empty of finite constant sheaves on basis opens. The finite sets can all be singletons.
Source: Stacks Project, Modules, Lemma 17.19.1 (Tag 0CAH)
(blueprint: lem-weil-pbc-sheaf-basis-surjection).

Proof:
1. Index by pairs consisting of a point and a germ of `F` there. Represent each germ by a
   section on a neighbourhood, then restrict to a basis neighbourhood of the point.
2. For each chosen section, restriction gives a map from the singleton constant sheaf on
   that basis open to the restriction of `F`. The extension-by-empty adjunction
   (lem-weil-pbc-sets-extension-by-empty-adjunction) gives a map to `F` which hits the
   chosen section on that open.
3. Form the coproduct of these extensions in sheaves, using
   lem-weil-pbc-sheaves-colimit-sheafification. Its universal property combines the maps
   into one morphism to `F` (def-weil-pbc-category-colimit).
4. Each germ is hit by the germ of the section in its indexed summand, so the resulting
   morphism is surjective on every stalk.
5. By lem-weil-pbc-sets-sheaf-epi-iff-stalks it is an epimorphism. Every coefficient set is
   a singleton, hence finite. -/
theorem exists_epi_extensionByEmptyConstant (X : TopCat.{u}) (B : Set (Set X))
    (hB : IsTopologicalBasis B) (F : X.Sheaf (Type u)) :
    ∃ (I : Type u) (U : I → Opens X) (S : I → Type u),
      (∀ i : I, (U i : Set X) ∈ B) ∧
      (∀ i : I, Finite (S i)) ∧
      (∀ i : I, Nonempty (Unique (S i))) ∧
      ∃ c : Cofan (fun i : I ↦ extensionByEmptyConstant (U i) (S i)),
        Nonempty (IsColimit c) ∧ ∃ φ : c.pt ⟶ F, Epi φ := by
  sorry

end TopCat
