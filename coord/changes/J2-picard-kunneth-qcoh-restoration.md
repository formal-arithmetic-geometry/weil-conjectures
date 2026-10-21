# AlgebraicGeometry.Scheme.Modules.picard_kunneth_qcoh

## Reason

Restore the assigned module from the quarantine path recorded in coord/rework.tsv.
The archive has a complete proof and zero local sorry bodies. Its public import
of Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations refers to a
withdrawn empty module. The canonical definitions used in the statement now live
in WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations.

Compiling the unmodified archive fails at line 128: Invalid field Modules on X
and Y; Lean reports that Modules is imported privately. Replacing the stale
public import with the canonical operations module makes the unchanged theorem
and proof compile cleanly in 3.3 seconds.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

All other Lean text is the archive at
quarantine/Sheaf/AlgebraicGeometry/PicardKunnethQcoh.lean.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The signature, docstrings, visibility, proof, affine-morphism public import and
both private proof imports are preserved verbatim. There are no new definitions,
instances, statements, holes or axioms. The existing node attachment is preserved;
its lean.note records this restoration. Its two proof steps still describe the
unchanged conjunction proof from picard_kunneth_iso_exists and
picard_kunneth_functoriality. All proof dependencies and the unit route stay.
No target statement or definition changes, so target semantic review is unaffected.

## Users

The read-only tools/downstream.py query reports unknown module(s), because the
assigned item is absent from lean/. Searches across lean/ and quarantine/ find
no current direct importer or external theorem application. PicardH1ProductSpanning
mentions the theorem in its docstring but its present Lean proof applies
picard_h1_product_spanning_bypass. Scanning every node's stmt_deps, proof_deps and
proof-step uses identifies lem-sc-picard-h1-product-spanning as the sole actual
DAG parent. Its dependency is preserved, as are all archived source and attachments.
The quarantine status does not authorize withdrawing this item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | J2 | Restored; canonical public import. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | DAG parent; same theorem interface and operations, no adaptation. |

No consumer fails because of this import correction; no forced adaptation is
needed. An independent importer probe compiled in 2.8 seconds with only a public import
of the restored item, checking the theorem and the canonical scalar operations.
The axiom print reports propext, Classical.choice, Quot.sound and inherited
sorryAx from existing dependencies. The validation-only probe was removed
before delivery.

## Status

landed 20261021T012405-L-2184446 2026-10-21 (merge of deliver/J2/Sheaf.AlgebraicGeometry.PicardKunnethQcoh)
