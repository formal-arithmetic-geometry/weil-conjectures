/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q59
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.FinitePresentationArrowsDescent
import Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem

/-!
# Fppf sheafification preserves affine limit continuity

Source: Stacks Project, Spaces and Limits, Tag 049O, lemma-sheafify-finite-presentation
(blueprint: lem-sfb-fppf-sheafification-affine-continuity).
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Sheafifying a set-valued presheaf on the big fppf site preserves continuity on
nonempty directed inverse systems of affine schemes over the base.

Source: Stacks Project, Spaces and Limits, Tag 049O, lemma-sheafify-finite-presentation
(blueprint: lem-sfb-fppf-sheafification-affine-continuity).

Proof:
1. For any presheaf G, represent its plus sections by matching families, and their equality
   by equality on a common covering refinement, using
   lem-weil-pbc-site-plus-construction-presheaf. By lem-pc-fppf-affine-refinement,
   representing and equality covers over affines can be finite affine fppf covers,
   hence standard covers as in lem-sfb-standard-fppf-cover-limit-descent.
2. Fix a standard cover at a stage. Its base changes are covers by
   lem-trf-fppf-covering-base-change. Components and pairwise overlaps are affine by
   lem-weil-pbc-morphism-affine-schemes-affine and lem-weil-pbc-affine-morphism-permanence.
   Their limits are the corresponding components and overlaps at the limit by
   lem-weil-pbc-scheme-over-limit and def-pc-fibre-product. Passing to a directed tail
   preserves set colimits by lem-weil-pbc-filtered-colimit-sets-elementwise.
3. Continuity for G on these systems gives continuity of the matching-family sets
   of def-weil-pbc-site-plus-construction: lift their finitely many components to one
   stage, and their finitely many matching equations to a later stage, using eventual
   equality in lem-weil-pbc-filtered-colimit-sets-elementwise. The same argument for two
   families proves injectivity. An empty cover has a singleton matching-family set.
4. For surjectivity for G-plus, descend a representing standard cover by
   lem-sfb-standard-fppf-cover-limit-descent, and lift its family by step 3.
   The restriction formula of lem-weil-pbc-site-plus-construction-presheaf identifies
   its class with the original section.
5. For injectivity, represent both sections at a common stage and choose a standard
   equality-refinement cover at the limit. Descend that cover by
   lem-sfb-standard-fppf-cover-limit-descent and its finitely many maps to the two
   representing covers by lem-weil-pbc-finite-presentation-arrows-descent. The required
   hypotheses follow from lem-weil-pbc-affine-scheme-qcqs,
   lem-weil-pbc-qcqs-morphism-permanence, and affine transitions. Step 3 makes the
   pulled-back families equal at a later stage; the plus equality criterion then
   identifies the original colimit elements.
6. Apply steps 2--5 first to F and then to F-plus. By
   lem-weil-pbc-sheafification-plus-theorem, double-plus is naturally isomorphic to
   sheafification compatibly with its unit. Naturality with respect to the limit
   projections transfers bijectivity to the displayed canonical comparison map. -/
theorem fppfSheafification_affineContinuity
    (B : Scheme.{u}) (F : (Over B)ᵒᵖ ⥤ Type (max (u + 1) v))
    (hF : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (D : Iᵒᵖ ⥤ Over B) (_hD : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
      (c : Cone D) (_hc : IsLimit c),
      Function.Bijective (colimit.desc (D.op ⋙ F) (F.mapCocone c.op)))
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over B) (hD : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
    (c : Cone D) (hc : IsLimit c) :
    Function.Bijective
      (colimit.desc (D.op ⋙ sheafify (fppfTopology.over B) F)
        ((sheafify (fppfTopology.over B) F).mapCocone c.op)) := by
  sorry

end AlgebraicGeometry.Scheme
