# AlgebraicGeometry.Scheme.lisse_on_stratum_interiors

## Reason

Complete the retirement listed in `coord/retire-items.tsv`, under the human hand-off
in `coord/changes/retire-sheaf-twins-20261020.md`. The item already has zero textual
holes. The existing upstream twin proves the same statement. The sole spelling
difference in the public signature is `IsLisseEtaleSheafOfSets`, an abbreviation
of `IsFiniteLocallyConstantSheafOfTypes`. A scratch theorem applies the upstream
theorem directly to the entire old signature, with the same universe.

## Old

In `Sheaf.AlgebraicGeometry.LisseStratumInteriors`:

```lean
theorem lisse_on_stratum_interiors
    {Z : Scheme.{u}} (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (T : Stratification Z)
    (hT : ∀ i : Fin T.n, IsLisseEtaleSheafOfSets
      ((etaleSetPullback (T.immersion i)).obj
        ((sheafCompose Z.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E))) :
    IsLisseEtaleSheafOfSets
      ((sheafCompose T.interiorUnion.toScheme.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} T.interiorUnion.ι).obj E))
```

The duplicate also contains the two proved private helpers `finiteLisse_of_iso`
and `finiteLisse_of_range_subset`. Neither has an external user.

## New

Use the existing theorem in `WeilConjectures.AlgebraicGeometry.LisseStratumInteriors`:

```lean
theorem lisse_on_stratum_interiors
    {Z : Scheme.{u}} (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (T : Stratification Z)
    (hT : ∀ i : Fin T.n, IsFiniteLocallyConstantSheafOfTypes
      ((etaleSetPullback (T.immersion i)).obj
        ((sheafCompose Z.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E))) :
    IsLisseEtaleSheafOfSets
      ((sheafCompose T.interiorUnion.toScheme.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} T.interiorUnion.ι).obj E))
```

Withdraw the duplicate with `deleted.txt`. No source-library file is edited. The
upstream private helpers implement the same fibre-product descent and gluing proof;
the first uses the already proved `isFiniteSheaf_of_finite_algClosed_stalks` to
handle the separably closed stalk predicate. Reattach the item's DAG node to this
upstream theorem and record that comparison in its proof dependencies. All parent
edges remain: the result is still needed, with the same declaration name and type.
The unit route stays unchanged. Empty schemes, empty strata and an empty interior
cover require no nonemptiness assumption in either signature or proof.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.LisseStratumInteriors --uses
AlgebraicGeometry.Scheme.lisse_on_stratum_interiors` reports zero downstream modules
and only the item itself as a textual name user in the Sheaf root. A search of both
Lean roots and quarantine finds no importer of the duplicate. The listed historical
consumer `Sheaf.AlgebraicGeometry.GenericFiniteSourceLisse` has already retired;
its DAG attachment and current upstream implementation use the upstream twin.
`WeilConjectures.lean` already imports the upstream twin. Both the upstream theorem
source and its actual consumer were copied to scratchpad and compiled unchanged
through lcompile.py. A separate exact-old-signature application compiled and its
axiom check, as well as the upstream theorem's, lists only propext, Classical.choice,
and Quot.sound.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LisseStratumInteriors | S1 | Withdraw duplicate; zero holes. |
| WeilConjectures.AlgebraicGeometry.LisseStratumInteriors | unclaimed | Existing provider; unchanged. |
| WeilConjectures.AlgebraicGeometry.GenericFiniteSourceLisse | unclaimed | Existing consumer already uses twin; unchanged and compiled. |
| WeilConjectures | unclaimed | Already imports upstream twin; unchanged. |

No target statement or definition changes. No target statement review is reopened.

## Status

landed 20261021T011034-L-2031050 2026-10-21 (merge of deliver/S1/Sheaf.AlgebraicGeometry.LisseStratumInteriors)
