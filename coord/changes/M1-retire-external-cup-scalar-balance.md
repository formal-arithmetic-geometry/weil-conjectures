# AlgebraicGeometry.Scheme.Modules.external_cup_scalar_balance

## Reason

Retire the duplicate Sheaf module in favor of its adopted upstream twin, following
coord/retire-items.tsv and the human-approved hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The assigned module contains zero holes.
The complete source diff shows the same public import, statement, definitions and
mathematical proof. Differences are copyright/spacing, two local instance names,
and grouping three consecutive rewrites into one rw invocation in a private proof.
No upstream file or target statement is changed.

## Old

The module Sheaf.AlgebraicGeometry.ExternalCupScalarBalance declares:

```lean
theorem external_cup_scalar_balance (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (G : Y.Modules)
    (p q : ℕ) (r : k) (a : scalarCohomology f F p) (b : scalarCohomology g G q) :
    externalCup f g F G p q a (r • b) = externalCup f g F G p q (r • a) b
```

The DAG attachment for lem-sc-external-cup-scalar-balance names this Sheaf module.

## New

The identical theorem signature and complete proof are retained in
WeilConjectures.AlgebraicGeometry.ExternalCupScalarBalance. The duplicate Sheaf file
is withdrawn through deleted.txt, and the DAG attachment names the retained module
and path. The statement, proof dependencies and blueprint unit route remain intact.
No mathematical dependency node is removed and no target semantic change occurs.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.AlgebraicGeometry.PicardExternalCupScalarComparison | unchanged upstream | Already imports the retained twin and applies the same theorem twice; compiled unchanged. |

There are zero current direct Lean importers of the retired module. The retirement
manifest's single listed consumer, Sheaf.AlgebraicGeometry.PicardExternalCupScalarComparison,
has already been retired; its DAG node points at the upstream consumer in the table.
The only DAG parent still cites lem-sc-external-cup-scalar-balance, which is preserved
with its original declaration name and a corrected module attachment. A scan of Lean
sources, quarantined Lean files, nodes and unit records finds no other live module/path
reference requiring migration. Neither of the two renamed local instances has an
external reference. There are zero Sheaf/WeilConjectures twin pairs in either retained
source import closure (254 modules for the theorem, 401 for its consumer).

Validation: lcompile.py compiled a scratch copy of the unchanged upstream theorem
in 13.4 seconds and its unchanged consumer in 8.0 seconds. The appended axiom probe
reports only propext, Classical.choice and Quot.sound. Scratch sources are outside the
delivery lean/ tree and are not part of the packet.

## Status

landed 20261020T160108-L-3325852 2026-10-20 (merge of deliver/M1/Sheaf.AlgebraicGeometry.ExternalCupScalarBalance)
