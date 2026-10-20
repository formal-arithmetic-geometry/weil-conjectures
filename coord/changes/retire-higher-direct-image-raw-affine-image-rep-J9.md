# AlgebraicGeometry.Etale.exists_higher_image_raw_affine_image_rep

## Reason

Retire the quarantined Sheaf twin in favour of the official library theorem,
as assigned by the human's retirement hand-off. The synced import environment
of the Sheaf root encounters duplicate declarations. The official twin provides
the identical theorem statement and proof body. No upstream file or target
statement is edited.

## Old

The theorem was provided by the quarantined module
`Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep`.
Its sole consumer imported it with:

```lean
import Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep
```

## New

The theorem is provided by the existing official module
`WeilConjectures.AlgebraicGeometry.HigherDirectImageRawAffineImageRep`.
The consumer is restored from the current sheaf-dag quarantine source with
this proof import:

```lean
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawAffineImageRep
```

All consumer declarations and proofs remain verbatim. The original Sheaf path
is listed in deleted.txt. The node sbc-lem-higher-image-raw-affine-image-rep
points to the official module and file; its statement and dependencies stay.
No mathematical statement or definition changes, and no holes are introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed; cluster restoration assigned to J9 | Only the proof import changes; verified by lcompile.py and the delivery dry run. |

A search of all Lean sources under lean/ and quarantine/ finds no other
importer of the retired module. Its sole DAG parent still uses the same node
and declaration through the official module. The unit route is unchanged.

## Status

landed 20261020T153750-L-2989004 2026-10-20 (merge of deliver/J9/Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep)

The consumer has zero direct holes. The delivery tool now accepts retirement
of the quarantined path; the previous deletion-gate failure is resolved.
The quarantine sources and launcher scripts are untouched.

C-38662 return repair: the previous reviewed head 38662b488fe failed to land
because this consumer changed after base e0d550965. The packet has been rebuilt
from the current quarantine consumer and the single import edit reapplied.
The current consumer retains hK and its original proof; the different official
comparison-epi signature is not substituted. The fresh server compile passed in
17.8 seconds; the dry run at eb7d47132d4 compiled and passed preflight. No quarantine source is changed.
