# AlgebraicGeometry.Scheme.finiteLocallyConstant_pullback_stratum

## Reason

Complete the retirement listed in `coord/retire-items.tsv` (row headed
`retire:Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum`), under the human's
2026-10-20 handoff in `coord/changes/retire-sheaf-twins-20261020.md`.
The Sheaf copy has zero textual holes and duplicates the existing proved upstream theorem.
Its predicate `IsLisseEtaleSheafOfSets` abbreviates the upstream predicate
`IsFiniteLocallyConstantSheafOfTypes`, so the full signatures are definitionally equal.
No source-library declaration, attribute, public import or proof changes.

## Old

In `Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum`:

```lean
theorem finiteLocallyConstant_pullback_stratum
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (S : Stratification X)
    (hS : ∀ i : Fin S.n, IsLisseEtaleSheafOfSets
      ((etaleSetPullback (S.immersion i)).obj
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E))) :
    ∀ i : Fin S.n, IsLisseEtaleSheafOfSets
      ((etaleSetPullback ((S.pullback g).immersion i)).obj
        ((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj E)))
```

## New

Withdraw the Sheaf copy using `deleted.txt`. The same declaration is already proved in
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum`:

```lean
theorem finiteLocallyConstant_pullback_stratum
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (S : Stratification X)
    (hS : ∀ i : Fin S.n, IsFiniteLocallyConstantSheafOfTypes
      ((etaleSetPullback (S.immersion i)).obj
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E))) :
    ∀ i : Fin S.n, IsFiniteLocallyConstantSheafOfTypes
      ((etaleSetPullback ((S.pullback g).immersion i)).obj
        ((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj E)))
```

The node `lem-stage3-finite-lc-pullback-stratum` now attaches to that upstream declaration.
The upstream proof implements the recorded five steps: compare abelian and set inverse
images on the original stratum; pull back its finite local constancy along the first
projection; use the Cartesian equation and `upperStarComp`; forget the group structure;
and compare with set inverse image on the new stratum. The node's proof dependencies stay.

The only parent node is `lem-weil-pbc-constructible-etale-set-pullback`. Its Lean module
already imports the upstream stratum module and applies this theorem verbatim to the
pulled-back stratification. Thus no parent dependency is deleted or replaced, and the
unit route stays intact. The actual replacement is this existing complete proof, not
an inference from the absence of current importers. No target statement or definition
changes; no target statement review is reopened.

The exact former Sheaf signature is checked by an `example` applying the upstream
theorem in scratch Lean. The upstream theorem and the unchanged parent use only
`propext`, `Classical.choice`, and `Quot.sound`. Empty stratifications (the conclusion
has no indices), empty schemes and empty stalks do not introduce extra hypotheses.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum
--uses finiteLocallyConstant_pullback_stratum` finds zero downstream modules and
only the declaration's own textual occurrence. Direct searches of both Lean roots
and quarantine find no remaining import or use of the Sheaf copy. The upstream
parent is included below because it uses the declaration through the replacement.
The historical Sheaf parent has already been retired and is absent from `lean/`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum | N3 | Withdraw zero-hole duplicate. |
| WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullback | unclaimed | No edit; already imports and uses upstream twin. Checked unchanged. |

## Status

landed 20261021T011026-L-2029799 2026-10-21 (merge of deliver/N3/Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum)
