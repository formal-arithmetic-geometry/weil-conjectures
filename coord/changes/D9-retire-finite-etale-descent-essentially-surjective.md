# AlgebraicGeometry.finiteEtaleDescent_essSurj

## Reason

Complete the retirement request in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective. Its recorded
one-hole duplicate has already been replaced by a declaration-free re-export
in D7's landed change retire-finite-etale-descent-data-existence. The upstream
proof is complete, and the DAG attachment already names it. Retire the remaining
unused wrapper, rather than introducing the duplicate declaration again.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective

/-!
Re-export the upstream finite etale descent theorem. The canonical datum and
its compatibility predicate are supplied by the upstream construction.
-/
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/FiniteEtaleDescentEssentiallySurjective.lean
via deleted.txt. The landing tool supplies an empty module. Keep the upstream
module and its declarations verbatim. Keep the node's existing upstream Lean
attachment and its mathematical dependencies, adding only a retirement note.

The replacement proof is the existing upstream finiteEtaleDescent_essSurj:
effective affine fpqc descent constructs the descended scheme; finiteness and
etaleness descend along the cover; the two invariant pullback projections
produce an isomorphism respecting transport. Its parent finiteEtaleDescent
already imports this upstream module directly and uses that theorem to obtain
EssSurj alongside Full and Faithful. No parent dependency changes are required:
D7's reviewed retirement has already reconciled that route with the current
source, and the same DAG node still supplies the essential-surjectivity step.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective | D9 | Withdraw unused wrapper. |
| WeilConjectures.AlgebraicGeometry.FiniteEtaleDescent | unclaimed; not adapted | Existing direct upstream import and application remain unchanged. |

The downstream script reports zero users of the wrapper. An exact search of
live Lean and quarantine sources finds no other import of its module. Scanning
all DAG statement/proof/step dependencies finds only lem-galois-descent as a
parent of lem-galois-descent-essentially-surjective; that parent is attached to
WeilConjectures.AlgebraicGeometry.FiniteEtaleDescent. No node attaches to the
Sheaf wrapper. The unit sk-prop-h2 has no realization attached to the wrapper.
No target statement or definition changes meaning.

Verification: the original wrapper compiled on the server. The original
upstream parent compiled individually, with appended diagnostic commands:
#print axioms for finiteEtaleDescent_essSurj and finiteEtaleDescent each reported
only propext, Classical.choice and Quot.sound (1.6 seconds). The diagnostic
copy is excluded from the delivery. The withdrawal gate independently checks
that no live importer remains.

## Status

landed 20261020T144242-L-2258561 2026-10-20 (merge of deliver/D9/Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective)
