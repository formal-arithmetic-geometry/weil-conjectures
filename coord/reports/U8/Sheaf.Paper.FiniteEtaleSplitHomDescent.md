## What changed

The item module now contains two named intermediate theorems, `finiteEtaleSplitHom_exists` and `finiteEtaleSplitHom_epi`, and combines them in a complete proof of `finiteEtaleSplitHom_descent`. The intermediate theorems are strict subparts: the first omits the epi conclusion, while the second assumes a candidate global map and proves only its epi property. Their proofs remain `sorry` with individual DAG nodes, as permitted for stage-3 decomposition. The original `FiniteEtaleModuleChart.Compatible` definition and target theorem signature are unchanged.

The parent proof is real Lean: it obtains the map from the existence theorem, constructs the required conjunction, and applies the epi theorem to the local maps. No additional imports are needed beyond the existing trace formula and Mathlib morphism imports.

## Proved and sorry left

- Closed: `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_descent`.
- Added split hole: `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_exists`, node `lem-sfb-finite-etale-split-hom-descent-existence`.
- Added split hole: `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_epi`, node `lem-sfb-finite-etale-split-hom-descent-epi`.
- Remaining holes in the item module: the two named intermediate theorems above (2).

This is a decomposition into the existence and epi-cancellation arguments, not a claim that the mathematical work has disappeared. No definition contains `sorry` and no axiom is introduced.

## No longer needed

The earlier attempted local-comparison helper modules were withdrawn before delivery; their paths are listed in `deleted.txt`. Their nodes remain in DAG history but are not proof dependencies of the delivered item. No existing public module or source-library declaration was changed.

The parent proof uses only the two new intermediate theorem declarations. The previously listed direct proof dependencies for localization, internal module equivalence and Hom-cover gluing are therefore represented inside those two split nodes and are not imported directly by the item.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan bundled two independent long arguments: constructing the glued map and proving its epimorphism. The declarations did not expose either as a standalone stage-3 statement. Splitting at this boundary gives strictly simpler, source-backed obligations and leaves a short, transparent combination proof. The mathematical target statement itself is unchanged.

## New nodes

`lem-sfb-finite-etale-split-hom-descent-existence` and `lem-sfb-finite-etale-split-hom-descent-epi` are realized as named intermediate theorems in the item module. The first is the compatible-map gluing conclusion. The second is local epi cancellation and global separatedness for a supplied map. Each node records the finite-etale splitting, weakly-etale localization, and sheaf-module gluing sources used by its proof.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
