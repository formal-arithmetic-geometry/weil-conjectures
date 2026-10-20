## What changed

Retire Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep in favour of
WeilConjectures.AlgebraicGeometry.HigherDirectImageRawAffineImageRep, as assigned
by the retirement hand-off. Restore its quarantined consumer,
Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi, at its original
path, changing only its proof import to the official twin. All consumer
declarations, signatures, docstrings and proof bodies remain verbatim.

The retired copy is listed in deleted.txt. The node
sbc-lem-higher-image-raw-affine-image-rep retains its statement, declaration,
proof plan and proof dependencies; only its lean attachment changes to the
official module and file, with existing=true and a retirement note. Its sole
DAG parent, sbc-lem-higher-image-colimit-comparison-epi, still uses this node
and the same declaration. No unit route changes. No upstream file, target
statement or quarantined source is edited.

The C-38662 return is repaired by rebuilding the packet against current
sheaf-dag. The consumer is currently quarantined at
quarantine/Sheaf/AlgebraicGeometry/HigherDirectImageColimitComparisonEpi.lean.
I reread that current source and reapplied only the proof-import migration;
its declaration (including hK), docstring and proof are preserved. In particular,
I did not substitute the differently stated official comparison-epi theorem.
The delivery tool constructs the new commit on its freshly fetched sheaf-dag.

Change record: coord/changes/retire-higher-direct-image-raw-affine-image-rep-J9.md.

## Proved and sorry left

This is a retirement repair with zero initial direct holes, zero holes closed,
zero holes added, zero remaining direct holes and zero split-off statements.
AlgebraicGeometry.Etale.exists_higher_image_raw_affine_image_rep is supplied
by the official twin with exactly the quarantined theorem's statement and
proof body. The restored consumer retains its complete proof of
AlgebraicGeometry.Etale.epi_higher_image_colimit_comparison.

A textual comparison from the public section onward confirms that the root
and twin have identical declarations and proofs. A source comparison confirms
the consumer's single import edit. A parsed JSON comparison confirms that
only the node's lean attachment changes. A fresh server lcompile.py check
compiled the consumer in 17.8 seconds with exit code 0 and no diagnostics.
The repaired delivery dry run passed at eb7d47132d4, including its compile
and axiom probe. The packet has zero direct sorry declarations.

## No longer needed

Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep and its consumer's
import of that module are retired. The consumer instead imports the official
WeilConjectures twin. Searches of lean/ and quarantine/ find no other consumer
of the Sheaf module. The existing DAG node and all its mathematical dependencies
remain needed through the official theorem. No upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked because deliver3.py rejected deletion of an
already-quarantined path. The current tool explicitly accepts a path found in
quarantine/, so that failure is resolved without changing launcher scripts or
bypassing a gate. The explicit retirement assignment supersedes restoring the
duplicate declaration: the consumer is restored using the official theorem,
and the retired root is withdrawn through deleted.txt. The original quarantine
files remain untouched for the maintainer's verification.

The reviewed delivery 38662b488fe did not land because the consumer changed
on sheaf-dag after its base e0d550965. This retry restores the current quarantine
source rather than carrying an old base. Comparing current source with the
repaired consumer gives exactly one changed import; comparing the current
node with the packet gives only the intended lean attachment change. The
quarantine archive is preserved. This is the requested conflict repair of an
already-reviewed retirement, with no new mathematical or definition change.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
