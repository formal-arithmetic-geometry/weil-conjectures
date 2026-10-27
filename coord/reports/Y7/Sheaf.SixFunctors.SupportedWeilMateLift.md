## What changed

Filled both proofs of `Sheaf.SixFunctors.SupportedWeilMateLift`. The coefficient
square is proved by transposing through the target exceptional adjunction. The
main theorem specializes a proved private generic argument to rational and
common-stage Frobenius equivalences. Its proof gives mate normalization and
uniqueness, the three-factor formula, shifts, the lifted adjunction, the full
Hom action, the unique triangle isomorphism, closed-counit recovery, and both
functoriality clauses. Existing signatures, definitions and public imports stay
unchanged. Added a private proof import of
`WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction`.

## Proved and sorry left

Closed `WeilConjectures.sf_supportedWeilMate_coefficient` and
`WeilConjectures.sf_supportedWeilMateLift`, both attached to
`lem-sf-supported-weil-mate-lift`: 2 of 2 original holes. Added no holes; no
`sorry` remains in the delivered module. Every private helper is proved.
This is a proof from existing declarations, including the existing automorphism
stage equivalence theorems, rather than a new decomposition.

## No longer needed

Removed the unused private import `Sheaf.CategoryTheory.MateIsoAlongEquivalences`.
The declared dependency `lem-weil-mate-iso-along-equivalences` is replaced here by
the already proved source-library `IsoAlgebra.mateIso`, imported through the
existing fixed-pair adjunction module. The dependency
`lem-sf-open-closed-weil-mate-structures` and its module
`Sheaf.SixFunctors.OpenClosedWeilMateStructures` are not needed by these proofs:
`S.a_mate` already supplies their required normalization. The DAG proof and
proof dependency list now record these facts. No module is withdrawn, and no
claim about these dependencies being globally unused is made. The unit route is
preserved; its `realized` fields contain no fixed node route.

## Where the brief, the DAG or earlier work was wrong

The planned generic mate invertibility and shift calculations already have
proved source-library implementations. The open/closed comparison theorem is
unnecessary after its normalization is included in the input record. The
triangle uniqueness assumption can be used for a pulled source triangle by
precomposing with the inverse of one constructed triangle isomorphism. No
statement correction or definition repair was needed.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
