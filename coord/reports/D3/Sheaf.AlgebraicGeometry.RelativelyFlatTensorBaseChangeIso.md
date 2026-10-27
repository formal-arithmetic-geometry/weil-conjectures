## What changed

Restored lean/Sheaf/AlgebraicGeometry/RelativelyFlatTensorBaseChangeIso.lean as a
public compatibility re-export of the adopted source module
WeilConjectures.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso. The preserved
quarantine archive already has a complete proof, but its withdrawn dependency imports
make it fail against the current library. The adopted source has the exact theorem
signature and complete K-flat tensor/base-change argument. No duplicate theorem or
private helper is introduced, and the quarantine archive is unchanged.

Updated only the Lean attachment of lem-pc-relatively-flat-tensor-base-change-iso to
the adopted source declaration. Its statement, five proof steps, proof dependencies,
parent dependencies and unit route are retained. The two theorem signatures compare
textually equal. The source-library boundary is respected: no source file changes.

The restored shim compiled without warnings in 2.4 seconds. A separate consumer
reproducing the complete archived signature compiled in 3.7 seconds by applying the
adopted theorem to all original arguments. Both the consumer and source theorem's
#print axioms show only propext, Classical.choice and Quot.sound. Import-direction
checking permits the source import. The consumer preserves ordinary termwise pullback
of G, arbitrary E, both derived-category assumptions, every universe and hypothesis;
zero complexes and empty schemes require no additional restrictions.

Change record:
coord/changes/D3-relatively-flat-tensor-base-change-source-compatibility.md.

## Proved and sorry left

This is a zero-hole quarantine repair: 0 of 0 local sorry holes closed, 0 added,
0 remaining and 0 split off. AlgebraicGeometry.relativelyFlat_tensor_baseChange_iso
(node lem-pc-relatively-flat-tensor-base-change-iso) is supplied by its existing,
fully proved source declaration. No new proof of that already proved theorem is claimed.
No declaration with sorry is left anywhere in this delivery.

## No longer needed

The duplicate archived theorem implementation and private tensorPullback_kFlat helper
are not restored; the source theorem supplies the full proof. The shim needs none of
the five archived direct proof imports: RelativelyFlatDerivedBaseChangeComplex,
KFlatDerivedTensorComparison, DerivedPullbackTensorProduct, KFlatResolution and
KFlatPullback. The source theorem retains all five corresponding source imports and
the same mathematical argument; no dependency node or module is pruned.

The old public Mathlib and WeilConjectures imports are public through the source
module. The two old public Sheaf imports, DerivedPullback and
SingleComplexBaseChangeStalkCondition, are empty withdrawn modules; their source
counterparts are public imports of the source theorem module. No mathematical
statement dependency is removed. No module is withdrawn in this packet.

The quarantined ProperSupportPerfectDirectImage parent and the live source
CartesianTensorDataComparison parent still require this result. Their DAG dependencies
are preserved. The unit sk-thm-picard-semicon still realizes its recorded statement and
semicontinuity proof step; this compatibility repair bypasses neither.

## Where the brief, the DAG or earlier work was wrong

The assigned item is absent from lean/ and listed in coord/rework.tsv, rather than a
live module containing sorry. Its archive has zero holes. Compiling the unchanged
archive reports unknown CochainComplex.isKFlat_pullback and privately imported
public-signature identifiers derivedPullback and Scheme.Modules.tensorPullback.
Several former Sheaf dependency paths are now empty withdrawn modules. Re-exporting
the adopted theorem restores both the theorem and its public statement environment.

The retained-twin table previously warned against importing both dependency clusters.
This repair imports only the adopted source cluster. The exact archived-signature
consumer and its axiom check succeed. No second implementation, incompatible duplicate
cluster, new instance, new definition, or statement weakening is introduced.

The DAG's old Lean attachment pointed at the absent declaration; it now points at
the actual existing source theorem. Its proof plan already describes the source proof
and needs no change. No mathematical error in the theorem was found.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
