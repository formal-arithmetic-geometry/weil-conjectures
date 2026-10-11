/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Restricting a constant sheaf pushed forward from a closed subset

Source: Stacks Project, Etale Cohomology, proof of Lemma 59.82.1 (Tag 09ZG),
the displayed global-section identifications
(blueprint: lem-weil-pbc-closed-pushforward-constant-restriction).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, proof of Lemma 59.82.1 (Tag 09ZG), displayed identifications
(blueprint: lem-weil-pbc-closed-pushforward-constant-restriction).
The presheaf `G` below is exactly `V ↦ LC(V ∩ Z', S)` with restriction of maps.
Its inverse image is the sheafification of the presheaf pullback, and `eta` is the
presheaf adjunction unit (the colimit coprojection), followed below by `theta`.

Proof, following the node's five steps:
1. On `Z` form the sheaf `H(U) = LC(U ∩ Z', S)`. Restriction gives compatible maps
   from the diagram defining the presheaf pullback, hence a presheaf map to `H`
   by the colimit universal property (def-weil-pbc-category-colimit).
2. Factor through sheafification (def-weil-pbc-sheafification). Its global component
   is beta, and the factorization gives the asserted restriction compatibility.
3. The comparison is injective on stalks (lem-weil-pbc-sets-inverse-image-stalk and
   lem-weil-pbc-filtered-colimit-sets-elementwise): outside `Z'` use its open complement;
   inside `Z'`, equality of values and local constancy give equality on a neighbourhood.
4. Sections are determined by germs (lem-weil-pbc-sheaf-sections-determined-by-germs),
   so the comparison, and in particular beta, is injective on sections.
5. Every locally constant map on the intersection has local preimages: empty maps
   outside `Z'`, constant maps near points of the intersection. Injectivity makes
   these preimages agree on overlaps, and the sheaf axiom glues them. Thus beta is
   surjective. Taking `Z' = Set.univ` gives the parenthetical special case. -/
theorem closed_pushforward_constant_restriction
    (X : TopCat.{u}) (Z Z' : Set X) (hZ : IsClosed Z) (hZ' : IsClosed Z') (S : Type u) :
    let G : X.Presheaf (Type u) :=
      { obj := fun U ↦ LocallyConstant {x : X // x ∈ unop U ∧ x ∈ Z'} S
        map := fun {U V} f ↦ TypeCat.ofHom (LocallyConstant.comap
          ⟨fun x : {x : X // x ∈ unop V ∧ x ∈ Z'} ↦
              ⟨x.1, f.unop.le x.2.1, x.2.2⟩,
            continuous_subtype_val.subtype_mk _⟩)
        map_id := by intros; rfl
        map_comp := by intros; rfl }
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let P := (Presheaf.pullback (Type u) i).obj G
    let F := (presheafToSheaf (Opens.grothendieckTopology (TopCat.of Z)) (Type u)).obj P
    let eta := (Presheaf.pullbackPushforwardAdjunction (Type u) i).unit.app G
    let theta := (sheafificationAdjunction
      (Opens.grothendieckTopology (TopCat.of Z)) (Type u)).unit.app P
    ∃ beta : F.obj.obj (op ⊤) ≃ LocallyConstant {x : X // x ∈ Z ∧ x ∈ Z'} S,
      ∀ g : LocallyConstant Z' S,
        beta (theta.app (op ⊤)
          (P.map (homOfLE (show (⊤ : Opens Z) ≤ (Opens.map i).obj ⊤ from
            fun _ _ ↦ Set.mem_univ _)).op
            (eta.app (op ⊤) (LocallyConstant.comap
              ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩ g)))) =
          LocallyConstant.comap
            ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩ g := by
  sorry

end TopCat
