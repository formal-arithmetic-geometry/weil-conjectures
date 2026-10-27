# AlgebraicGeometry.properSupport_local_noetherian_model

## Reason

Restore the quarantined module named by coord/rework.tsv, preserving its declaration and
all mathematical dependencies. The archived module still imports the withdrawn Sheaf
DerivedPullback and DerivedPullbackComposition modules. Their declarations now live in
the adopted WeilConjectures modules, as their DAG attachments record. Redirect both
imports to those owners. The repaired module compiles on the server in 25.1 seconds.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
```

The full archived theorem signature and proof are preserved verbatim.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

The restored file is lean/Sheaf/AlgebraicGeometry/ProperSupportLocalNoetherianModel.lean.
No declaration signature, definition, proof, attribute or DAG dependency changes.
The public import now exposes the actual definition that the existing signature uses.
The composition import remains private because it is used only in the proof.

## Users

The downstream.py query refuses the currently quarantined module as unknown. Direct
searches of both lean/ and quarantine/ find exactly the parent below. Searching node
stmt_deps, proof_deps and proof-step uses also finds exactly its node,
lem-pc-proper-support-perfect-direct-image. No live Lean module currently imports the
item. Quarantine is not treated as evidence that the item is unnecessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed in the local snapshot | Quarantined parent calls the restored theorem with its existing signature; no adaptation. |

The parent destructures the same neighbourhood, model, properties and comparison iso;
its subsequent Noetherian perfect-direct-image argument is unchanged. The unit record
sk-thm-picard-semicon and its realized route are untouched. No target meaning changes.

## Status

landed 20261025T061038-L-2394762 2026-10-25 (merge of deliver/V9/Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel)
