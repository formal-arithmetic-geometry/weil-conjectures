# AlgebraicGeometry.Scheme.refinement_preserves_finite_lisse

## Reason

The assigned Sheaf module already contains zero holes and compiles. The adopted source
library also proves the same declaration, with an identical elaborated type. The local
predicate IsLisseEtaleSheafOfSets is an abbrev of the upstream predicate
IsFiniteLocallyConstantSheafOfTypes. Keep the source library verbatim and retire the
duplicate Sheaf module after changing its sole direct importer. This is a replacement
by an existing complete proof, not withdrawal of the mathematical result.

The 2026-10-20 kept-twins inventory marked this module DIFFERENT because the source
restated the theorem. Here a Lean probe confirms the source theorem proves the local
signature without any conversion lemma or added hypothesis. Its axiom set is exactly
propext, Classical.choice, Quot.sound. No adopted-source declaration, signature,
attribute, public import or body is edited.

## Old

Module: Sheaf.AlgebraicGeometry.RefinementPreservesFiniteLisse.

```lean
theorem refinement_preserves_finite_lisse
    (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (T S : Stratification X) (hTS : T.Refines S)
    (hS : ∀ k : Fin S.n,
      IsLisseEtaleSheafOfSets
        ((etaleSetPullback (S.immersion k)).obj F)) :
    ∀ i : Fin T.n,
      IsLisseEtaleSheafOfSets
        ((etaleSetPullback (T.immersion i)).obj F)
```

Its sole direct importer, Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement, has:

```lean
import Sheaf.AlgebraicGeometry.RefinementPreservesFiniteLisse
```

## New

The duplicate module is withdrawn through deleted.txt. The consumer instead has:

```lean
import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
```

The retained, already proved source declaration is:

```lean
theorem refinement_preserves_finite_lisse
    (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (T S : Stratification X) (hTS : T.Refines S)
    (hS : ∀ k : Fin S.n,
      IsFiniteLocallyConstantSheafOfTypes
        ((etaleSetPullback (S.immersion k)).obj F)) :
    ∀ i : Fin T.n,
      IsFiniteLocallyConstantSheafOfTypes
        ((etaleSetPullback (T.immersion i)).obj F)
```

The refinement-preservation node now attaches to this upstream declaration, preserving
all mathematical dependencies. Its parent node records the direct upstream application
and keeps the same dependency node. No target statement or definition changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RefinementPreservesFiniteLisse | H7 | Retired duplicate; its theorem remains available from the source module. |
| Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement | unclaimed | Replace one proof import; statement and proof body are identical. |
| Sheaf.AlgebraicGeometry.IrreducibleLisseStrata | unclaimed | Transitive consumer; no source edit, statement and proof preserved. |

The direct and transitive consumer list was checked with tools/downstream.py and rg.
No claim or rework entry holds either consumer. The sole DAG parent is
lem-weil-pbc-irreducible-refinement; it retains the dependency with its new source
attachment. No rework row names the item or either consumer; the DAG search found only this parent. The unit
sk-prop-sf-cbc has no realized entry removed; its route is preserved. The upstream
refinement module imports only its existing WeilConjectures dependencies.

## Status

landed 20261020T221215-L-4157276 2026-10-20 (merge of deliver/H7/Sheaf.AlgebraicGeometry.RefinementPreservesFiniteLisse)
