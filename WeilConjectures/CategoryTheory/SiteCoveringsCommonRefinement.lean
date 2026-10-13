/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Common refinements of coverings of a site

Source: Stacks Project, Sites, Lemma 7.10.5 (Tag 00W6) and its proof
(blueprint: lem-weil-pbc-site-coverings-common-refinement).
-/

@[expose] public section

universe u w w' t

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Precoverage

/-- Any choice of the pairwise fibre products gives a covering, and the specified projections
are refinement morphisms with the two coordinate index maps. Source: Stacks Project,
Sites, Lemma 7.10.5 (Tag 00W6)
(blueprint: lem-weil-pbc-site-coverings-common-refinement).

Proof: Apply site axiom (iii) (def-weil-pbc-sites-and-cohomology) to the second covering
along each member of the first, using the given pullback squares. The resulting families
cover each `E.X i`. Apply axiom (ii) to compose these families with `E`. Reindex the sigma
index type by its equivalence with the product to obtain the displayed covering presieve.
The maps `q` and `p`, with index maps `Prod.fst` and `Prod.snd`, satisfy the commuting
triangles by the structure-map definition and the pullback-square equation, respectively.
These are precisely morphisms of coverings over the identity as in
 def-weil-pbc-site-plus-construction (b). -/
theorem siteCoverings_common_refinement {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] {U : C}
    (E : ZeroHypercover.{w} J U) (F : ZeroHypercover.{w'} J U)
    (W : E.I₀ × F.I₀ → C)
    (q : ∀ ij : E.I₀ × F.I₀, W ij ⟶ E.X ij.1)
    (p : ∀ ij : E.I₀ × F.I₀, W ij ⟶ F.X ij.2)
    (h : ∀ ij : E.I₀ × F.I₀, IsPullback (p ij) (q ij) (F.f ij.2) (E.f ij.1)) :
    Presieve.ofArrows W (fun ij => q ij ≫ E.f ij.1) ∈ J U ∧
    (∃ r : PreZeroHypercover.Hom
      { I₀ := E.I₀ × F.I₀, X := W, f := fun ij => q ij ≫ E.f ij.1 }
      E.toPreZeroHypercover, r.s₀ = _root_.Prod.fst ∧ HEq r.h₀ q) ∧
    (∃ r : PreZeroHypercover.Hom
      { I₀ := E.I₀ × F.I₀, X := W, f := fun ij => q ij ≫ E.f ij.1 }
      F.toPreZeroHypercover, r.s₀ = _root_.Prod.snd ∧ HEq r.h₀ p) := by
  sorry

/-- Any finite family of coverings of an object has a common refinement.
Source: Stacks Project, Sites, Lemma 7.10.5 (Tag 00W6), finite iteration
(blueprint: lem-weil-pbc-site-coverings-common-refinement).

Proof: Induct on the cardinality of the finite family. For the empty family use the
singleton identity covering, which is a covering by axiom (i) of
 def-weil-pbc-sites-and-cohomology. At the induction step use the binary common-refinement
construction above to refine the previous common refinement and the new covering.
Compose its projection to the previous refinement with each previously obtained
refinement morphism (def-weil-pbc-site-plus-construction (b)); its other projection refines
the new covering. Product index types stay in the same universe under finite iteration. -/
theorem siteCoverings_finite_common_refinement {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] {U : C}
    (K : Type t) [Finite K] (E : K → ZeroHypercover.{w} J U) :
    ∃ W : ZeroHypercover.{w} J U, ∀ k : K, Nonempty (ZeroHypercover.Hom J W (E k)) := by
  sorry

end CategoryTheory.Precoverage
