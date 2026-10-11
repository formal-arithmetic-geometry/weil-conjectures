import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.CategoryTheory.SiteCechComplex

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

/-! # Filtered colimits of injectives are Čech-acyclic on a quasi-compact basis

Source: literature/stacks-project/cohomology.tex, Lemma 01FF proof and Lemma 01EW
(blueprint: lem-sc-topological-filtered-injective-cech-acyclic).
-/

/-- A filtered colimit of injective abelian sheaves on a space with a quasi-compact
basis is Čech-acyclic on finite quasi-compact covers, and has no higher cohomology
on quasi-compact opens.
Source: literature/stacks-project/cohomology.tex, Lemma 01FF proof and Lemma 01EW
(blueprint: lem-sc-topological-filtered-injective-cech-acyclic).

Proof: identify sections of the colimit on every quasi-compact finite intersection
with the filtered colimit of the sections of the injectives; finite products commute
with filtered colimits, so the Čech complex is the filtered colimit of the complexes
for the injectives. Each latter complex is acyclic in positive degree by
`lem-weil-pbc-site-injective-cech-acyclic`, and exactness is preserved by filtered
colimits of abelian groups. The Čech vanishing criterion
`lem-weil-pbc-site-cech-vanishing-criterion` then gives vanishing of higher derived
cohomology on every quasi-compact open.
-/
theorem topological_filtered_injective_cech_acyclic
    {X : Type u} [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (hbasis : TopologicalSpace.Opens.IsBasis
      {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    (hpairs : ∀ U V : TopologicalSpace.Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : TopologicalSpace.Opens X) : Set X))
    {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : Discrete I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [HasColimit F]
    (hI : ∀ i : I, Injective (F.obj (Discrete.mk i))) :
    (∀ (U : TopologicalSpace.Opens X), IsCompact (U : Set X) →
      ∀ (T : Type u) [Finite T] (f : T → TopologicalSpace.Opens X)
        (hom : ∀ t, f t ⟶ U)
        (hcompact : ∀ t, IsCompact ((f t : TopologicalSpace.Opens X) : Set X))
        (hcover : Presieve.ofArrows f hom ∈ (Opens.pretopology X).toPrecoverage U)
        (S : SiteCechComplex f hom),
        ∀ p : ℕ, 0 < p →
          IsZero ((S.cohomologyFunctor p).obj (colimit F).obj)) ∧
      (∀ (U : TopologicalSpace.Opens X), IsCompact (U : Set X) →
        ∀ q : ℕ, 0 < q → IsZero (H' (colimit F) q U)) := by
  sorry

end CategoryTheory.Sheaf
