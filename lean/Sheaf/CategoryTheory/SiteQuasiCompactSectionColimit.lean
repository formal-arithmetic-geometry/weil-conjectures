/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-! # Sections of filtered colimits over quasi-compact site objects

Source: Stacks Project, Sites, Definition 090H and Lemma 0738 (2), (4);
Modules on Sites, Lemma 03CO
(blueprint: lem-sfb-site-quasi-compact-section-colimit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

/-- The section comparison is injective over a quasi-compact site object and is an
isomorphism if finite coverings with quasi-compact pairwise overlaps are cofinal.
Quasi-compactness is written out as the finite-image refinement condition; the
refining covering in this condition need not itself be finite. Fibre products in
selected finite coverings are specified by their universal property, so no global
pullback assumption is imposed on the site.

Source: Stacks Project, Sites, Definition 090H and Lemma 0738 (2), (4);
Modules on Sites, Lemma 03CO
(blueprint: lem-sfb-site-quasi-compact-section-colimit).

Proof, following the five steps of the node:
1. Form the sectionwise presheaf colimit P. Its sheafification is the sheaf colimit
   by lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact. Underlying-set
   sheafification agrees with abelian sheafification by
   lem-pc-sites-sheafification-underlying-sets. Thus
   lem-weil-pbc-site-sheafification-sections-local gives local lifts from P and
   local equality of sections of P with equal images in the sheaf colimit.
2. By lem-weil-pbc-abelian-groups-forget-filtered-colimits and
   lem-weil-pbc-filtered-colimit-sets-elementwise, each element of P has a stage
   representative, and equality at a fixed stage is witnessed by one later arrow.
3. A stage section mapping to zero vanishes eventually on a covering by steps 1-2.
   Quasi-compactness refines this covering through only finitely many original
   members. Filteredness gives a cocone on the finite star of vanishing arrows.
   The resulting stage section restricts to zero on the entire refining cover,
   hence is zero by sheaf separatedness. Representatives then prove injectivity.
   If the refinement is empty, separatedness for the empty cover suffices.
4. Given a section of the sheaf colimit, refine a local-lifting cover by a finite
   cover from the cofinal system. Choose stage representatives of its local lifts
   and move them to one stage using filteredness. For an empty cover choose any
   stage, which exists since the indexing category is nonempty.
5. On each pairwise fibre product the difference of two local representatives
   maps to zero. Step 3 and quasi-compactness of that product kill the difference
   at a later stage. A cocone on the finite star of these arrows makes all local
   representatives match at once, and the stage sheaf glues them. Separatedness
   identifies their image with the original section, proving surjectivity.
   The cofinal finite-cover hypothesis also makes W quasi-compact: its finite
   refinement has an index map of finite image. Step 3 therefore gives
   injectivity at W as well. The bijective homomorphism is an isomorphism.
   Empty covers glue the unique section and require no separate hypothesis.

All sets, group values and small diagrams are taken in one containing universe,
as in the node's proof. `colimit.post` is induced by the evaluated sheaf-colimit
coprojections, not an arbitrary comparison homomorphism. -/
theorem quasiCompact_section_colimit
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (_hJ : J.IsSiteForCoverings)
    {D : Type u} [SmallCategory D] [IsFiltered D]
    (G : D ⥤ Sheaf J.toGrothendieck AddCommGrpCat.{u}) (W : C) :
    ((∀ (A : Type u) (V : A → C) (f : ∀ a, V a ⟶ W),
        Presieve.ofArrows V f ∈ J W →
        ∃ (B : Type u) (T : B → C) (g : ∀ b, T b ⟶ W) (α : B → A)
          (h : ∀ b, T b ⟶ V (α b)),
          Set.Finite (Set.range α) ∧ (∀ b, h b ≫ f (α b) = g b) ∧
            Presieve.ofArrows T g ∈ J W) →
      Function.Injective (colimit.post G
        ((sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj (op W)))) ∧
    ((∀ (A : Type u) (V : A → C) (f : ∀ a, V a ⟶ W),
        Presieve.ofArrows V f ∈ J W →
        ∃ (B : Type u) (_ : Finite B) (T : B → C) (g : ∀ b, T b ⟶ W),
          Presieve.ofArrows T g ∈ J W ∧
          (∀ b, ∃ (a : A) (h : T b ⟶ V a), h ≫ f a = g b) ∧
          ∀ b b', ∃ (P : C) (p : P ⟶ T b) (q : P ⟶ T b'),
            IsPullback p q (g b) (g b') ∧
            ∀ (E : Type u) (Z : E → C) (k : ∀ e, Z e ⟶ P),
              Presieve.ofArrows Z k ∈ J P →
              ∃ (F : Type u) (Y : F → C) (l : ∀ t, Y t ⟶ P) (β : F → E)
                (m : ∀ t, Y t ⟶ Z (β t)),
                Set.Finite (Set.range β) ∧ (∀ t, m t ≫ k (β t) = l t) ∧
                  Presieve.ofArrows Y l ∈ J P) →
      IsIso (colimit.post G
        ((sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj (op W)))) := by
  sorry

end CategoryTheory.Sheaf
