# cupCechResolution_beta_class_pairing

## Reason

The assigned module and its node are absent from the current source checkout.
Restore the previously reviewed declarations from the dedicated repair note.
The repair changes no existing theorem signature or definition.

## Old

The source modules Sheaf.Paper.CechCupResolutionBetaClassPairing and
Sheaf.Paper.CechCupSignedAxisPairing are absent from the current source checkout.
Their prior signatures are preserved verbatim in the restored modules and node records.

## New

Restore both modules with their prior signatures. The beta-axis theorem uses three
proved private helpers and the signed-axis theorem. The latter remains the named
lower-level hole, with its source and complete proof in words. The main theorem
requires no extra cover or coefficient hypothesis.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CechCupResolutionBetaClassPairing | G3 | Restore prior interface and proof. |
| Sheaf.Paper.CechCupSignedAxisPairing | new | Restore signed-axis dependency. |

No present library module imports the absent beta-axis module. No outside module
was adapted. The unrelated anonymous-instance collision in the global batch probe
remains; it cannot be fixed by edits to these two modules.

## Status

landed 20261014T052438-L-1913314 2026-10-14 (merge of deliver/G3/Sheaf.Paper.CechCupResolutionBetaClassPairing)
