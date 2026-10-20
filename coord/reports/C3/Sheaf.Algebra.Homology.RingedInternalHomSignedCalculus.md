## What changed

Proved five original holes in
`Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`:
`moduleMonoidalPreadditive` derives additivity from preservation of biproducts,
`moduleFlatResolution` uses the existing functorial flat resolution,
`derivedMonoidal_eq_localization` applies a generic instance equality,
`totalTensor_eq_native` identifies the two totalizations definitionally, and
`tensorParameterShift_naturality` combines the two shift naturality equations.
No definition, signature, import, or unscoped option changed. The final module
uses the original transparency settings. The generic equality helper avoids
expensive kernel comparison after specializing to sheaves.

## Proved and sorry left

Closed five of six original holes, by the five declaration names above. Added
zero holes. The unchanged sorry is
`CategoryTheory.SignedRingedHom.normalizedAdjunction_existsUnique`, tagged
`lem-weil-pbc-ringed-internal-hom-exact-restriction`.

## No longer needed

None. All original imports are retained for the existing statements and
constructions. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No node has this module as its primary Lean attachment. Its docstrings refer to
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, currently attached to
`RingedInternalHomShiftOfUniverses`.

The native monoidal equality is proved in a generic category before specializing
to module sheaves; this avoids expensive kernel checking of the concrete
instance comparison. The general closed symmetric-monoidal existence theorem
does not directly supply evaluation-normalized uniqueness required by
`normalizedAdjunction_existsUnique`.

Two earlier dry runs were killed with exit 137 without a push. The unbuffered
retry identified an unscoped option change; the original option has been restored.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
