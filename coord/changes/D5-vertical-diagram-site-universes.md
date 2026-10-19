# CategoryTheory.diagramSiteTopology

## Reason

The coefficient tower category is defined on ℕ × T.ProEt. The old product-site
API ties both category universes and their hom universes together, and represents
its index as Jᵒᵖ. It cannot be applied directly to ℕ × T.ProEt with independent
scheme and coefficient universes. Generalize the same explicit construction to
arbitrary categories and an arbitrary coefficient universe, and retain every old
public signature as a specialization. The module is unclaimed.

## Old

```lean
def diagramSiteTopology (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) : GrothendieckTopology (Jᵒᵖ × C) where
  sieves X := {S | S.functorPullback (Prod.sectR X.1 C) ∈ K X.2}
  top_mem' X := by
    change (⊤ : Sieve X.2) ∈ K X.2
    exact K.top_mem _
  pullback_stable' {X Y} {S} f hS := by
    apply K.superset_covering _ (K.pullback_stable f.2 hS)
    intro Z g hg
    change S (Prod.mkHom (𝟙 Y.1) g ≫ f)
    change S (Prod.mkHom (𝟙 X.1) (g ≫ f.2)) at hg
    simpa using S.downward_closed hg (Prod.mkHom f.1 (𝟙 Z))
  transitive' {X} {S} hS R hR := by
    apply K.transitive hS
    intro Y f hf
    have H := hR (show S ((Prod.sectR X.1 C).map f) from hf)
    change (R.pullback ((Prod.sectR X.1 C).map f)).functorPullback
      (Prod.sectR X.1 C) ∈ K Y at H
    rwa [Sieve.functorPullback_pullback] at H

```

The sheaf criterion was proved directly for the original same-universe signature.

## New

```lean
def diagramSiteTopology (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) : GrothendieckTopology (Jᵒᵖ × C) :=
  verticalDiagramSiteTopology Jᵒᵖ C K

```

The original structure definition is definitionally equal to its new body.
`verticalDiagramSiteTopology` and `verticalDiagramSite_isSheaf_iff` provide the
same construction and criterion on J × C with independent category universes.
The old criterion is obtained by specializing to Jᵒᵖ, preserving its signature.
There is no change to covering sieves, ring sheaves, or existing mathematical meanings.
The private set-valued criterion is generalized in exactly the same way.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DiagramSiteTopology | unclaimed | General API; old signatures preserved. |
| Sheaf.CategoryTheory.DiagramSiteSheafEquivalence | unchanged consumer | Compiled unchanged against the generalized construction. |
| Sheaf.CategoryTheory.DiagramSiteModuleEquivalence | unchanged consumer | Compiled unchanged against the generalized construction. |
| Sheaf.CategoryTheory.DiagramSiteRealization | unchanged consumer | Compiled unchanged; uses the same existence theorem. |
| Sheaf.Paper.SmoothPurityCoefficientTowersAbelian | D5 | Uses the general vertical sheaf criterion to prove abelian axioms. |

`tools/downstream.py --uses CategoryTheory.diagramSiteTopology` finds only the
topology module and the two direct equivalence modules as textual users. The
remaining transitive importers see definitionally equal old declarations and
unchanged signatures. The two direct equivalences and their realization consumer
were recompiled unchanged against the delivered topology on 2026-10-19.

No consumer needs adaptation. No target statement or definition used by a target
changes its mathematical meaning.

## Status

landed 20261019T002524-L-2147180 2026-10-19 (merge of deliver/D5/Sheaf.Paper.SmoothPurityCoefficientTowersAbelian)
