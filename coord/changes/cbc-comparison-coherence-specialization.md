# AlgebraicGeometry.ProEtale.cbcComparisonPullbackCoherent

## Reason

Reuse the canonical coherence predicate and its proved theorem instead of asking Lean
to compare the entire expanded chosen-square equation during theorem application.
The prior Y7 delivery failed because it applied a conjunction whose module-coefficient
clause has no `Finite` binder to the compact-support conjunction that retains that
binder. The repaired proof specializes all three clauses separately and introduces
both the ring and finite instances before applying the module clause.

Only the coherence predicate is shared. Every compact-support construction, its
signature, defining body and visibility is retained verbatim. All original public
imports are retained to preserve the consumers' existing elaboration context.
The new public import is required by the predicate's public body.

The canonical predicate has the same identity and composition clauses. Its third
clause is `ComparisonSquareComponent (comparisonSquareData D g' f' f g sq) F`.
Expanding these two definitions substitutes the same canonical inverse-image,
comparison, identity, composition, and square maps into the old displayed equation.
The canonical and compact-support maps have identical defining expressions: the
site comparison is the componentwise identity, the direct-image comparison is the
same restriction comparison, and the inverse-image comparison is its normalized
conjugate. In particular the supplied `sq.w.symm` transport is retained. This is
a definitionally identical sharing of the predicate, not a change of hypotheses,
conclusion, coefficient universes or square data. No target signature is changed.

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
AlgebraicGeometry.ProEtale.cbcComparisonPullbackCoherent` reports only the defining
module as a textual user of this predicate. No external module uses the theorem
or the predicate. The two direct importers use the other, unchanged declarations,
or only their import context. All other transitive importers retain that API through
them. No consumer statement is made weaker, stronger or different.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportComparisonPullbackCoherence | S5 | Same coherence predicate; theorem now specializes the existing theorem coefficientwise. |
| Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport | N2 | Uses the unchanged adjunctions and comparison map; no source adaptation. |
| Sheaf.Paper.PbcUniformCompleteTriangulated | Q5 | Does not use the changed predicate; no source adaptation. |

The repaired item and both unchanged direct importers compile against a fresh
sandbox artifact: the item in 7.1 seconds, finite transport in 52.1 seconds, and
the triangulated consumer in 6.0 seconds. No consumer adaptations are needed.

## Status

landed 20261019T192832-L-1874669 2026-10-19 (merge of deliver/S5/Sheaf.Paper.CompactSupportComparisonPullbackCoherence)
