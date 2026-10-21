## What changed

Restored the assigned quarantined module as a public re-export of the existing,
proved `WeilConjectures.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso`.
The historical module path now shares the canonical declaration provider. A
public `Sheaf.Algebra.Homology.KFlat` import retains the historical
`IsAcyclicTensorKFlat` spelling, definitionally equal to `IsKFlatTensor`.
The DAG node's Lean attachment names the canonical source provider. Its statement,
statement dependencies, proof steps, proof dependencies and unit route stay intact.
No adopted source file or quarantine archive is changed.

Change record: `coord/changes/V8-affine-representative-canonical-reexport.md`.

Validation: lcompile.py compiled the restored module (2.2 seconds) and a separate
compatibility probe (4.6 seconds). The probe imports both paths together with the
canonical source-model consumer, repeats the complete old theorem signature and
applies the canonical theorem with every original argument. It also checks
`P.IsAcyclicTensorKFlat = P.IsKFlatTensor` by rfl. The canonical theorem and the
old-signature proof print only propext, Classical.choice and Quot.sound as axioms.
The probe is retained in the sandbox scratchpad and is not a delivered module.

## Proved and sorry left

This is the zero-hole rework listed in `coord/rework.tsv`, not a new proof or a
decomposition. The archive already has zero holes, and the restored module has
zero holes. Holes closed: none (0 of 0). Holes added: none (0). Sorries left: none.
The canonical theorem is
`AlgebraicGeometry.exists_affineBaseChangeIntoPullback_representativeIso`
(node `lem-pc-affine-base-change-source-representative-iso`). Its complete proof
remains in the source library.

## No longer needed

Removed the duplicate local private localization helper and duplicate theorem
provider by using the existing proved source module. The old direct private import
`Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality` is unnecessary in this
compatibility module: the canonical proof imports its upstream implementation.
The old public `WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback`
interface is still exported transitively through the canonical module.

No mathematical node or module is pruned. All five original proof dependencies
remain used by the canonical proof. The archived parent
`Sheaf.Algebra.Homology.AffineBaseChangeSourceModel` and its DAG dependency stay
preserved; the source-library parent is unchanged. No withdrawal or deleted.txt.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ because it was quarantined, not because
its representative-independence statement was withdrawn. Its archived proof has
zero sorries. The adopted source module already proves the same theorem under
the same name, with `IsKFlatTensor` replacing the definitionally equal historical
spelling. A direct restoration would keep a second declaration provider.
The generic expectation to close a sorry is inapplicable to this zero-hole repair.
The current re-export resolves the duplication and preserves the old interface.

The source-only downstream query (--allow-missing) found zero live importers of
the historical module. The quarantine search found its source-model parent,
whose exact original hypothesis and call interface is covered by the probe.
The existing upstream source-model consumer is also included in the import probe.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
