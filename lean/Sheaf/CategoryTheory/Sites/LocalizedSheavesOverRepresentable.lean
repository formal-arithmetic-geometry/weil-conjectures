/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Localized sheaves over a sheafified representable

Source: Stacks Project, Sites, Tag 00Y1, lemma-essential-image-j-shriek, and
lemma-describe-j-shriek in Section 00XZ
(blueprint: lem-weil-pbc-localized-sheaves-over-representable).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- Sheaves on the localized site are sheaves over the sheafified representable.
Source: Stacks Project, Sites, Tag 00Y1, lemma-essential-image-j-shriek, and
lemma-describe-j-shriek in Section 00XZ
(blueprint: lem-weil-pbc-localized-sheaves-over-representable).

The functor `P` is the disjoint-union presheaf with its projection to `yoneda.obj U`;
`e` specifies its sections, restrictions, projection, and action on sheaf arrows.
The forward functor of `E` is naturally isomorphic, over the sheafified representable,
to the sheafification of `P`. The equivalences `r` identify its inverse with the
specified fibres and specify restrictions and the action on arrows.

Proof, following the six steps of the node:
1. Form the fibre sheaf. Naturality preserves the fibre condition; a matching family
glues in the original sheaf and its image equals the required representable section
by separatedness. Localized coverings are those of the original site
(def-pur-localized-ringed-site; def-weil-pbc-sites-and-cohomology).
2. Form the disjoint-union presheaf, project to the representable, and sheafify.
The universal property extends the projection and all arrows uniquely
(def-weil-pbc-sheafification).
3. Send a slice section to the sheafification of its pair. Local equality and local
representatives show this is injective and surjective: refine until the first
coordinate is the specified arrow, then glue in the slice sheaf
(lem-weil-pbc-site-sheafification-sections-local).
4. Forget the arrow in a fibre pair and extend through sheafification. To prove
injectivity, represent both sections locally, use equality of their images, and
refine until their arrows agree; separatedness finishes the argument.
5. To prove surjectivity, locally represent the image of a section in the sheafified
representable. The resulting fibre pairs glue using injectivity from step 4
(lem-weil-pbc-site-sheafification-sections-local).
6. The two comparisons are natural by their formulas and uniqueness of extensions.
Their triangles hold on pairs, hence after sheafification. These give the unit and
counit of `E`. No subcanonicity or arbitrary pullback hypothesis is used. -/
theorem exists_localizedSheavesOverRepresentable
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [HasWeakSheafify J.toGrothendieck (Type u)] (U : C) :
    ∃ (P : Sheaf (J.toGrothendieck.over U) (Type u) ⥤ Over (yoneda.obj U))
      (e : ∀ (H : Sheaf (J.toGrothendieck.over U) (Type u)) (X : C),
        (P.obj H).left.obj (op X) ≃ Σ a : X ⟶ U, H.obj.obj (op (Over.mk a))),
      (∀ (H : Sheaf (J.toGrothendieck.over U) (Type u)) (X : C)
        (z : (P.obj H).left.obj (op X)),
        (P.obj H).hom.app (op X) z = (e H X z).1) ∧
      (∀ (H : Sheaf (J.toGrothendieck.over U) (Type u)) (X Y : C)
        (b : Y ⟶ X) (a : X ⟶ U) (s : H.obj.obj (op (Over.mk a))),
        e H Y ((P.obj H).left.map b.op ((e H X).symm ⟨a, s⟩)) =
          ⟨b ≫ a, H.obj.map (Over.homMk b rfl).op s⟩) ∧
      (∀ (H H' : Sheaf (J.toGrothendieck.over U) (Type u)) (f : H ⟶ H')
        (X : C) (a : X ⟶ U) (s : H.obj.obj (op (Over.mk a))),
        e H' X ((P.map f).left.app (op X) ((e H X).symm ⟨a, s⟩)) =
          ⟨a, f.hom.app (op (Over.mk a)) s⟩) ∧
      ∃ E : Sheaf (J.toGrothendieck.over U) (Type u) ≌
          Over ((presheafToSheaf J.toGrothendieck (Type u)).obj (yoneda.obj U)),
        Nonempty (E.functor ≅ P ⋙ Over.post (presheafToSheaf J.toGrothendieck (Type u))) ∧
        ∃ r : ∀ (F : Over
            ((presheafToSheaf J.toGrothendieck (Type u)).obj (yoneda.obj U))) (X : Over U),
            (E.inverse.obj F).obj.obj (op X) ≃
              {s : F.left.obj.obj (op X.left) |
                F.hom.hom.app (op X.left) s =
                  (toSheafify J.toGrothendieck (yoneda.obj U)).app (op X.left) X.hom},
          (∀ (F : Over
              ((presheafToSheaf J.toGrothendieck (Type u)).obj (yoneda.obj U)))
            (X Y : Over U) (b : X ⟶ Y) (s : (E.inverse.obj F).obj.obj (op Y)),
            (r F X ((E.inverse.obj F).obj.map b.op s)).val =
              F.left.obj.map b.left.op (r F Y s).val) ∧
          (∀ (F G : Over
              ((presheafToSheaf J.toGrothendieck (Type u)).obj (yoneda.obj U)))
            (f : F ⟶ G) (X : Over U) (s : (E.inverse.obj F).obj.obj (op X)),
            (r G X ((E.inverse.map f).hom.app (op X) s)).val =
              f.left.hom.app (op X.left) (r F X s).val) := by
  sorry

end CategoryTheory
