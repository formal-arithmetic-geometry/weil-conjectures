/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E1
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.Basic
import Sheaf.Topology.BasisSheafSectionsGerms

/-!
# Extending a sheaf of abelian groups from a basis

Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009N and 009Q
(blueprint: lem-weil-pbc-sheaf-on-basis-extends).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite TopologicalSpace

namespace TopologicalSpace.Opens

/-- A presheaf of abelian groups with unique gluing on an intersection-closed basis extends
 to a sheaf on the space, with group isomorphisms on basis opens commuting with restrictions.
Source: Stacks Project, Section 009H, Tags 009M, 009N and 009Q
(blueprint: lem-weil-pbc-sheaf-on-basis-extends).

Proof:
1. Form the stalks of the basis presheaf as colimits, with restriction-compatible germ maps
   (`def-weil-pbc-basis-presheaf-stalk`). By `lem-weil-pbc-basis-sheaf-sections-germs`, for a
   basis open `U` the germ map is injective and its image consists exactly of families of germs
   locally represented by sections on basis opens (Stacks 009M).
2. On any open `W`, take the families of germs locally represented by basis sections. Restrict
   by restricting the families. This predicate is stable under restriction: refine a representing
   basis neighbourhood by one contained in its intersection with the smaller open. It is local:
   a local representation on a neighbourhood is also one on `W`. Thus
   `lem-weil-pbc-local-predicate-sections-sheaf` makes these families a sheaf of sets (009N/007Y).
3. These families form a subgroup of the product of stalks: zero is locally represented by zero;
   sums and negatives are represented after intersecting the representing basis neighbourhoods
   and restricting their sections. Germ maps are homomorphisms. Restrictions are coordinate
   projections, hence homomorphisms, so this is a sheaf of abelian groups (009Q).
4. For a basis open, the germ map into the extension is a bijective group homomorphism by
   step 1. Its inverse is the required group isomorphism. Compatibility of germs with
   restrictions gives the displayed compatibility for every section of the extension.

Cover indices may be empty. The index universe contains the universe of all basis opens;
coverings with larger index types can be reindexed by their image in the basis, since agreement
on intersections forces equal sections for repeated opens. -/
theorem exists_sheaf_extension_of_basis_gluing
    (X : TopCat.{u}) (B : Set (Opens X)) (hB : IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (F : Bᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (hglue : ∀ (U : B) (I : Type (max u v w)) (V : I → {W : B // W ≤ U}),
      (⨆ i, (V i).val.val) = U.val →
      ∀ s : ∀ i, F.obj (op (V i).val),
        (∀ i j,
          (F.map (homOfLE
            (show (⟨(V i).val.val ⊓ (V j).val.val, hcap (V i).val (V j).val⟩ : B) ≤
              (V i).val from
              inf_le_left (a := (V i).val.val) (b := (V j).val.val))).op).hom (s i) =
          (F.map (homOfLE
            (show (⟨(V i).val.val ⊓ (V j).val.val, hcap (V i).val (V j).val⟩ : B) ≤
              (V j).val from
              inf_le_right (a := (V i).val.val) (b := (V j).val.val))).op).hom (s j)) →
        ∃! t : F.obj (op U),
          ∀ i, (F.map (homOfLE (V i).property).op).hom t = s i) :
    ∃ Fext : TopCat.Sheaf AddCommGrpCat.{max u v} X,
      ∃ iota : ∀ U : B, Fext.presheaf.obj (op U.val) ≅ F.obj (op U),
        ∀ (U V : B) (hVU : V ≤ U) (t : Fext.presheaf.obj (op U.val)),
          (iota V).hom.hom
              ((Fext.presheaf.map (homOfLE (show V.val ≤ U.val from hVU)).op).hom t) =
            (F.map (homOfLE hVU).op).hom ((iota U).hom.hom t) := by
  sorry

end TopologicalSpace.Opens
