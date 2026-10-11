module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Cohomology and closed immersion pushforward

Source: literature/stacks-project/cohomology.tex, Lemma 02UV
(blueprint: lem-sc-cohomology-closed-immersion-pushforward)

## Main statements

* `cohomology_closed_immersion_pushforward`: cohomology is invariant under
  pushforward along a closed embedding.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace

universe u

namespace TopCat

/-- Source: literature/stacks-project/cohomology.tex, Lemma 02UV
(blueprint: lem-sc-cohomology-closed-immersion-pushforward).

For a closed embedding of topological spaces, the cohomology of an abelian
sheaf agrees with that of its direct image. The proof uses exactness of direct
image, vanishing of its higher derived functors, and the Leray comparison.
-/
theorem cohomology_closed_immersion_pushforward
    {Z X : TopCat.{u}}
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    (F : TopCat.Sheaf AddCommGrpCat Z) (p : ℕ) :
    Nonempty
      (@CategoryTheory.Sheaf.H' (Opens Z) _ (Opens.grothendieckTopology Z) _
          (HasExt.standard _) F p ⊤ ≅
        @CategoryTheory.Sheaf.H' (Opens X) _ (Opens.grothendieckTopology X) _
          (HasExt.standard _) ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj F) p ⊤) := by
  sorry

end TopCat
