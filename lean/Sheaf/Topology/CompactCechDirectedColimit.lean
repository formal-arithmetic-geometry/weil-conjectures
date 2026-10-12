/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.Spaces
public import Sheaf.CategoryTheory.SiteCechComplex

/-!
# Directed colimits and finite compact Čech complexes

Source: Stacks Project, Cohomology, Tag 01FF, the comparison of Čech complexes
(blueprint: lem-sc-compact-cech-cohomology-directed-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- Finite compact Čech cohomology preserves an existing directed colimit of abelian
sheaves on a space with a compact open basis and compact intersections.

Source: Stacks Project, Cohomology, Lemma 01FF, the Čech-complex comparison.
(blueprint: lem-sc-compact-cech-cohomology-directed-colimit).

Proof: the compact-basis and compact-intersection hypotheses ensure that sections on
every compact chosen intersection preserve the directed colimit, by 01FF's degree-zero
argument. In degree k the tuple index Fin (k+1) → T is finite, so its product commutes
with filtered colimits of abelian groups. The resulting identifications commute with
restriction maps and finite alternating sums, and hence with all differentials and
cocone maps. Colimits of complexes are calculated degreewise. Exactness of filtered
colimits of abelian groups identifies the homology of this colimit complex with the
colimit of its homology groups. The identification respects the cocone legs, proving
preservation of the given colimit. This works also for the empty covering, where each
term is the zero group, and for the empty open. No injectivity of the diagram objects
is used. -/
theorem compact_siteCech_cohomology_preserves_directedColimit
    (X : Type u) [TopologicalSpace X]
    (hbas : ∀ (V : Set X), IsOpen V → ∀ x ∈ V, ∃ W : Set X, IsOpen W ∧
      IsCompact W ∧ x ∈ W ∧ W ⊆ V)
    (hint : ∀ (V W : Set X), IsOpen V → IsOpen W → IsCompact V → IsCompact W →
      IsCompact (V ∩ W))
    {T : Type u} [Finite T] {U : TopologicalSpace.Opens X}
    {f : T → TopologicalSpace.Opens X} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom)
    (hcompact : ∀ (p : ℕ) (a : Fin (p + 1) → T),
      IsCompact ((S.W p a : TopologicalSpace.Opens X) : Set X))
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (p : ℕ) :
    PreservesColimit F
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        S.cohomologyFunctor p) := by sorry

end CategoryTheory.Sheaf
