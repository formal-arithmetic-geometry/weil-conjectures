# AlgebraicGeometry.Scheme.exists_irreducible_lisse_stratification

## Reason

This listed retirement item has zero holes. The adopted source module
`WeilConjectures.AlgebraicGeometry.IrreducibleLisseStrata` already proves the
same theorem. The duplicate uses `IsLisseEtaleSheafOfSets`, which is an abbreviation
of the retained theorem's `IsFiniteLocallyConstantSheafOfTypes`. A Lean probe applied
the retained theorem to the old signature unchanged and checked its axioms.

## Old

Provider: `Sheaf.AlgebraicGeometry.IrreducibleLisseStrata`.

```lean
theorem exists_irreducible_lisse_stratification
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) :
    ∃ S : Stratification X, ∀ i : Fin S.n,
      IrreducibleSpace (S.domain i) ∧
        IsLisseEtaleSheafOfSets
          ((etaleSetPullback (S.immersion i)).obj
            ((sheafCompose X.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F))
```

## New

Provider: `WeilConjectures.AlgebraicGeometry.IrreducibleLisseStrata` (unchanged).

```lean
theorem exists_irreducible_lisse_stratification
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) :
    ∃ S : Stratification X, ∀ i : Fin S.n,
      IrreducibleSpace (S.domain i) ∧
        IsFiniteLocallyConstantSheafOfTypes
          ((etaleSetPullback (S.immersion i)).obj
            ((sheafCompose X.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F))
```

Withdraw the duplicate Sheaf module through `deleted.txt` and reattach
`lem-weil-pbc-irreducible-lisse-strata` to the retained source declaration. The
mathematical statement, proof dependencies, unit route, all target statements,
and all source-library declarations remain unchanged. No arbitrary data is chosen.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.IrreducibleLisseStrata --uses
exists_irreducible_lisse_stratification` reports zero downstream modules and only
the duplicate declaration itself as a textual use. A full source search found no
imports of the withdrawn module, including in quarantine. The historical consumer
`Sheaf.AlgebraicGeometry.ConstructibleFiniteStalkTests` has already been retired.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.AlgebraicGeometry.ConstructibleFiniteStalkTests | source library; no adaptation | The only current DAG parent already imports and uses the retained source theorem. Its original file compiles unchanged. |

All DAG parents were checked through `stmt_deps`, `proof_deps`, and proof-step
`uses`: the only dependent node is
`lem-weil-pbc-constructible-finite-stalk-tests`, already attached to the source
module in the table. Its dependency on the retained node stays. The unit's
`realized` entries do not attach this duplicate module separately. No parent
replacement argument is required: the existing adopted proof is exactly the
replacement, verified against the old signature, and the node is preserved.

## Status

landed 20261021T013815-L-2338571 2026-10-21 (merge of deliver/H3/Sheaf.AlgebraicGeometry.IrreducibleLisseStrata)
