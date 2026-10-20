# Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful

## Reason

Complete the retirement listed in `coord/retire-items.tsv`. D7's landed
`retire-finite-etale-descent-data-existence.md` already replaced the duplicate
with a public re-export of the proved upstream theorem and repointed
`lem-galois-descent-fully-faithful` to that upstream declaration. Remove the
remaining unused wrapper. This is a retirement of the wrapper, not of its
mathematical statement or upstream proof.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful

/-!
Re-export the upstream finite etale descent theorem. The canonical datum and
its compatibility predicate are supplied by the upstream construction.
-/
```

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/FiniteEtaleDescentFullyFaithful.lean`
via `deleted.txt`. The delivery tool leaves the standard empty module stub:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The theorem `AlgebraicGeometry.finiteEtaleDescent_fullyFaithful` remains in
`WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful` with its
complete proof, signature, and imports unchanged. No definitions change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful | E5 | unused wrapper withdrawn |

`tools/downstream.py` reports zero downstream modules and zero uses through
this wrapper. A search of `lean/` and `quarantine/` finds no importer.
The sole mathematical parent, `lem-galois-descent`, still uses
`lem-galois-descent-fully-faithful`. Its module
`WeilConjectures.AlgebraicGeometry.FiniteEtaleDescent` directly imports the
upstream theorem and applies it in its complete proof. The node attachment
already points upstream, so no DAG edit is needed or made. The unit record
`sk-prop-h2` and its realized steps are untouched. No target meaning changes.

Server verification of the existing wrapper succeeds in 1.4 seconds, and
`#print axioms AlgebraicGeometry.finiteEtaleDescent_fullyFaithful` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Status

landed 20261020T144245-L-2258989 2026-10-20 (merge of deliver/E5/Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful)
