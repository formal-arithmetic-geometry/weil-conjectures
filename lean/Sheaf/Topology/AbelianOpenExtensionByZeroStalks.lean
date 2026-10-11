/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Sheaf.Topology.AbelianOpenExtensionByZero

/-! # Stalks of extension by zero of an abelian sheaf

Source: Stacks Project, Sheaves, Lemma 00A5, parts (2), (3), (5), and Modules,
Lemma 02UT (blueprint: lem-sc-topological-extension-by-zero-stalks).
-/

universe w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- The stalk is the original stalk on U and zero outside U, naturally in the sheaf.
The isomorphisms are specified by their values on germs of sections on opens contained
in U, so they are the canonical maps, rather than arbitrary abstract isomorphisms.
Under the canonical restriction-stalk identification, the counit induces the identity.
Source: Stacks, Sheaves, Lemma 00A5 and Modules, Lemma 02UT
(blueprint: lem-sc-topological-extension-by-zero-stalks).

Proof: (1) Apply `stalkFunctor_map_unit_toSheafify_isIso`, the recorded
`lem-weil-pbc-stalk-sheafification-space`, to the extension presheaf. This preserves germs.
(2) Outside U, every neighborhood has no inclusion into U, so its section group is the
empty direct sum, zero. Its filtered colimit and therefore its sheafified stalk are zero.
(3) Inside U, neighborhoods contained in U are cofinal. Each has precisely one summand,
with the original restriction maps. The colimit comparison followed by (1) is the
canonical stalk isomorphism, with the displayed germ equation.
(4) All comparisons commute with sheaf morphisms because restrictions, direct-sum
injections and the sheafification unit do. The presheaf counit is identity on each sole
summand and zero on an empty sum. Thus its stalk map, after the two canonical germ
identifications, is identity on F_x. This gives the final compatibility equation. -/
theorem abelianOpenExtensionByZero_stalks (X : TopCat.{w}) (U : Opens X) :
    ∃ e : ∀ (x : U)
        (G : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U)),
        TopCat.Presheaf.stalk (G.obj) x ≅
          TopCat.Presheaf.stalk (((abelianOpenExtensionByZero U).obj G).obj) x.val,
      (∀ (x : U) (G : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U))
        (V : Opens X) (hV : V ≤ U) (hx : x.val ∈ V),
        TopCat.Presheaf.germ (G.obj) ((Opens.map U.inclusion').obj V) x hx ≫ (e x G).hom =
          abelianOpenExtensionSection U G V hV ≫
            TopCat.Presheaf.germ (((abelianOpenExtensionByZero U).obj G).obj) V x.val hx) ∧
      (∀ (x : U)
        (G H : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U)) (α : G ⟶ H),
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{w} x).map α.hom ≫ (e x H).hom =
          (e x G).hom ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{w} x.val).map
            ((abelianOpenExtensionByZero U).map α).hom) ∧
      (∀ (G : TopCat.Sheaf AddCommGrpCat.{w} ((Opens.toTopCat X).obj U))
        (x : X), x ∉ U →
          IsZero (TopCat.Presheaf.stalk (((abelianOpenExtensionByZero U).obj G).obj) x)) ∧
      (∀ (F : TopCat.Sheaf AddCommGrpCat.{w} X) (x : U),
        ∃ r : TopCat.Presheaf.stalk ((abelianOpenRestriction U F).obj) x ≅
            TopCat.Presheaf.stalk (F.obj) x.val,
          (∀ (V : Opens X) (hV : V ≤ U) (hx : x.val ∈ V),
            TopCat.Presheaf.germ ((abelianOpenRestriction U F).obj)
                ((Opens.map U.inclusion').obj V) x hx ≫ r.hom =
              eqToHom (congrArg (fun W : Opens X ↦ F.obj.obj (op W))
                (openImage_preimage_eq U V hV)) ≫ TopCat.Presheaf.germ (F.obj) V x.val hx) ∧
          (e x (abelianOpenRestriction U F)).hom ≫
              (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{w} x.val).map
                (abelianOpenCounit U F).hom = r.hom) := by
  sorry

end TopCat.Sheaf
