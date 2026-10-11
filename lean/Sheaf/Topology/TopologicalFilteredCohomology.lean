module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace TopCat

/-! # Cohomology commutes with filtered colimits on quasi-compact spaces
Source: literature/stacks-project/cohomology.tex, Lemma 01FF
(blueprint: lem-sc-topological-filtered-cohomology).
-/

/-- On a space with a quasi-compact open basis whose pairwise intersections are
quasi-compact, cohomology over a quasi-compact open commutes with directed colimits.

Source: literature/stacks-project/cohomology.tex, Tag 01FF,
lemma-quasi-separated-cohomology-colimit (abelian sheaves: constant ring sheaf ℤ).
(blueprint: lem-sc-topological-filtered-cohomology).

Proof:
1. The colimit exists by lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact.
   View abelian sheaves as modules over the constant ring sheaf ℤ. By
   lem-weil-pbc-module-directed-colimit-underlying-sets their underlying set sheaves
   form a colimit. Every covering of a quasi-compact open admits a finite refinement
   by quasi-compact opens, with quasi-compact intersections. Apply
   lem-weil-pbc-sheaves-directed-colimit-sections to identify sections of the colimit
   with the colimit of sections, for every such open and every diagram.
2. By lem-weil-pbc-grothendieck-functorial-injective-embedding embed the diagram
   naturally into a diagram of injective sheaves Iᵢ. Let Qᵢ be the cokernels, giving
   a diagram of short exact sequences 0 → Fᵢ → Iᵢ → Qᵢ → 0.
3. Exact filtered colimits (lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact)
   give the short exact sequence 0 → colim Fᵢ → colim Iᵢ → colim Qᵢ → 0.
4. For finite covers by quasi-compact opens, Step 1 identifies the Cech terms of
   colim Iᵢ with colimits of the corresponding finite products of sections of Iᵢ.
   Exact filtered colimits of abelian groups preserve the acyclic Cech complexes.
   Apply lem-sc-topological-filtered-injective-cech-acyclic and
   lem-weil-pbc-site-cech-vanishing-criterion: positive cohomology of colim Iᵢ vanishes
   on every quasi-compact open.
5. Induct on q simultaneously for all quasi-compact opens. Degree zero is Step 1
   and H⁰(U,G) = G(U) (def-sc-topological-abelian-cohomology and
   def-weil-pbc-sites-and-cohomology). The natural long exact sequences from
   lem-weil-pbc-right-derived-universal-delta-functor, injective vanishing from
   lem-weil-pbc-derived-functor-injective-vanishing, and Step 4 identify the next
   degree as the cokernel of the preceding Iᵢ → Qᵢ cohomology maps. Exactness from
   lem-weil-pbc-filtered-colimit-abelian-groups-exact and the induction isomorphisms
   give the next comparison isomorphism, including degree one via sections.
6. Equivalently, each class comes from a stage and a stage class mapping to zero
   becomes zero at a later stage. These give surjectivity and injectivity of the
   canonical comparison map displayed below. -/
theorem topological_filtered_cohomology
    (X : Type u) [TopologicalSpace X]
    (hbas : ∀ (U : Set X), IsOpen U → ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧
      IsCompact V ∧ x ∈ V ∧ V ⊆ U)
    (hint : ∀ (U V : Set X), IsOpen U → IsOpen V → IsCompact U → IsCompact V →
      IsCompact (U ∩ V))
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u})
    (q : ℕ) (U : TopologicalSpace.Opens X) (hU : IsCompact (U : Set X))
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u})] :
    IsIso (colimit.desc
      (F ⋙ CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q ⋙
        (evaluation (Opens X)ᵒᵖ (AddCommGrpCat.{u})).obj (op U))
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q ⋙
        (evaluation (Opens X)ᵒᵖ (AddCommGrpCat.{u})).obj (op U)).mapCocone
        (colimit.cocone F))) := by
  sorry

end TopCat
