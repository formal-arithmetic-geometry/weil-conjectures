## What changed

Proved `AlgebraicGeometry.canonicalRelativeProj_restrict_proper` by assembling affine finite-generator presentations, using H-projective properness on each local relative Proj, transporting properness across the canonical restriction comparison, and applying target-locality. Added the comparison module with the one postponed comparison theorem. (Reviewer FIX: the three unnoded public aliases `canonicalRelativeProj`, `canonicalRelativeProjHom`, `canonicalRelativeProjLocal` were removed and inlined; the binder `hU` of the item was restored, so its statement is unchanged; the local properness step now cites `hProjective_properness`.)

## Proved and sorry left

Closed the original sorry in `AlgebraicGeometry.canonicalRelativeProj_restrict_proper` (1 of 1). The new comparison theorem `AlgebraicGeometry.exists_canonicalRelativeProj_restrict_iso` remains as one split-off sorry, with node `lem-trf-canonical-relative-proj-restriction-comparison`.

## No longer needed

`lem-trf-projective-bundle-quotient-geometry` is no longer used and was dropped from the item's proof_deps. The proof uses affine presentations, projective-implies-proper, and the new restriction comparison.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the explicit canonical relative-Proj restriction comparison required to transport local H-projective properness to the global restriction. This was split into a separate theorem.

## New nodes

`lem-trf-canonical-relative-proj-restriction-comparison` records the affine-local Proj comparison and is implemented by `Sheaf.TraceFormula.CanonicalRelativeProjRestrictionComparison`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.TraceFormula.CanonicalRelativeProjProperLocal": "08b8b19631b85ccba8d9d8f0a4e0ae63a40f9398", "Sheaf.TraceFormula.CanonicalRelativeProjRestrictionComparison": "badf74863871bc2315cab643bacd1a478f47c4bd"}, "results": {"Sheaf.TraceFormula.CanonicalRelativeProjProper": {"hash": "9f0bee42fa043dad663c2ea4f2c62b730e4ce55b", "status": "OK"}}, "seconds": 7, "time": "2026-10-28T08:08:57+0800", "transitive": 0, "version": 1}
```

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
