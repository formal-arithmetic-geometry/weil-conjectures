# AlgebraicGeometry.ProEtale.cbcComparisonPullbackCoherent

## Reason

The attempted specialization of the existing canonical coherence theorem to the
expanded compact-support predicate times out after 60 seconds. Share the existing
canonical predicate, as the support-site realization already does. This avoids
re-elaborating and comparing the expanded square equation. No file is split and
the compile limit is unchanged.

This is a definitionally identical refactor. The compact-support etale and
pro-etale pullback functors, adjunctions, and identity/composition/square maps have
the same bodies as their unprefixed counterparts. Both direct-image comparisons
use the componentwise identity on the same chosen fibre products. The inverse-image
comparison is their same conjugate. Substituting the fields of
`comparisonSquareData` into `ComparisonSquareComponent` gives exactly the third
clause below; the first two clauses are identical under these name expansions.
Identity maps, arbitrary composites, and the supplied Cartesian-square equality
transport are all retained. All coefficient categories, universes, and binders
are unchanged. No target signature or mathematical meaning changes.

The import of `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence` is public
because the shared predicate now occurs in a public definition. Its declarations
add no instances or attributes to this module.

## Old

```lean
def cbcComparisonPullbackCoherent : Prop :=
  (∀ (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology D),
    (cbcComparisonCoefficientPullbackIso D (𝟙 X)).hom.app F ≫
        (cbcProEtaleComparisonId D X).hom.app ((cbcComparisonCoefficientPullback D X).obj F) =
      (cbcComparisonCoefficientPullback D X).map ((cbcEtaleComparisonId D X).hom.app F)) ∧
  (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (F : Sheaf Z.smallEtaleTopology D),
    (cbcComparisonCoefficientPullback D X).map ((cbcEtaleComparisonComp D f g).hom.app F) ≫
        (cbcComparisonCoefficientPullbackIso D f).hom.app ((cbcEtaleComparisonPullback D g).obj F) ≫
        (cbcProEtaleComparisonPullback D f).map
          ((cbcComparisonCoefficientPullbackIso D g).hom.app F) =
      (cbcComparisonCoefficientPullbackIso D (f ≫ g)).hom.app F ≫
        (cbcProEtaleComparisonComp D f g).hom.app ((cbcComparisonCoefficientPullback D Z).obj F)) ∧
  (∀ (X' X Y' Y : Scheme.{u}) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : ChosenCartesianSquare g' f' f g)
      (F : Sheaf Y.smallEtaleTopology D),
    (cbcComparisonCoefficientPullbackIso D f').hom.app ((cbcEtaleComparisonPullback D g).obj F) ≫
        (cbcProEtaleComparisonPullback D f').map
          ((cbcComparisonCoefficientPullbackIso D g).hom.app F) ≫
        (cbcProEtaleComparisonSquare D sq).hom.app ((cbcComparisonCoefficientPullback D Y).obj F) =
      (cbcComparisonCoefficientPullback D X').map ((cbcEtaleComparisonSquare D sq).hom.app F) ≫
        (cbcComparisonCoefficientPullbackIso D g').hom.app
          ((cbcEtaleComparisonPullback D f).obj F) ≫
        (cbcProEtaleComparisonPullback D g').map
          ((cbcComparisonCoefficientPullbackIso D f).hom.app F))
```

## New

```lean
abbrev cbcComparisonPullbackCoherent : Prop :=
  ComparisonPullbackCoherent D
```

## Users

`tools/downstream.py Sheaf.Paper.CompactSupportComparisonPullbackCoherence --uses
AlgebraicGeometry.ProEtale.cbcComparisonPullbackCoherent` finds only the defining
module. A repository-wide text search finds no external reference to the predicate
or its theorem. The two direct importers below use other, unchanged declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportComparisonPullbackCoherence | Y7 | Same predicate; existing theorem is proved by the canonical comparison theorem. |
| Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport | N2 | Uses unchanged compact-support maps; no adaptation needed. |
| Sheaf.Paper.PbcUniformCompleteTriangulated | Q5 | No use of the changed predicate; no adaptation needed. |

The item compiles cleanly in 4.5 seconds. A separate validation tree compiles
this delivered item first, then both unchanged direct importers and the map-agreement
diagnostic against its compiled artifacts; all pass. The diagnostic checks by `rfl`
the equality of the site-base-change, direct-image, inverse-image, identity,
composition, and square isomorphisms. Its `#print axioms
cbcComparison_pullback_coherent` reports only `propext`, `Classical.choice`, and
`Quot.sound`. No consumer is edited.

All other downstream modules inherit the same definitions through these direct
importers. No consumer is edited. A target using this definition retains precisely
the same mathematical predicate; the independent reader can check the three
expanded clauses against the old definition above.

## Status

landed 20261019T112626-L-3963152 2026-10-19 (merge of deliver/Y7/Sheaf.Paper.CompactSupportComparisonPullbackCoherence)
