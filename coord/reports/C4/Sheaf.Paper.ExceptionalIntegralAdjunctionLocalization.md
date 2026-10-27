## What changed

Repaired `Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization` by constructing the
normalized adjunction directly from `A.adjunction.localization`. Rationalization of the
finite-Tor category is a localization after transport through the proof-changing equivalence.
Its endpoint shift is exactly the existing `integralRationalizationShift`.
`Functor.commShiftOfLocalization` supplies the raw left functor's shift and its normalized
comparison. Exactness descends through the localization, and the right shift and exactness
come from the adjunction. The localization counit formula proves the required normalization.

Added `rawRationalComparison`, the literal identity-component comparison of the integral
and tensor functors. Corrected `exists_raw_localized_identity_comparison` to require the
normalized counit and left shift square, and proved it: the right square follows from
identifying its comparison with the shift-compatible mate of the inverse left comparison.
Both added hypotheses are established by the parent proof. The parent theorem
`exists_integral_adjunction_raw_localization`, all existing public definitions, and the
canonical endpoint shifts retain their statements and data.

Updated the three existing DAG nodes to this proof. No intermediate hole is introduced.
A new definition node records the existing tensor data moved to a separate module to meet
the compile-time limit. The statement-change record is
`coord/changes/C4-normalized-raw-localization.md`. A search with `tools/downstream.py --uses`
and a source search find no caller of the corrected helper outside its own module.

The literal tensor definitions are publicly reexported from the new data module; their
names, signatures and data are preserved. This compile-time split is recorded in
`coord/changes/C4-raw-localization-data-module.md`. The original proof module still publicly
imports its original statement dependency.

The generic localization construction is checked over abstract categories and then applied to
the coefficient categories. This avoids repeatedly elaborating its shift and exactness proofs.
The tensor functor caches its existing full integral functor and its instances; after expanding
that cache the object and arrow data are unchanged. This refactor is recorded in
`coord/changes/C4-raw-tensor-functor-cache.md`.

Validation: the data module compiled in 38.4 seconds and the proof module in 56.6 seconds.
The unchanged direct importer `ExceptionalScalarMateLocalization` compiled in 28.5 seconds;
the external tensor-functor user `ExceptionalRationalStageLocalization` compiled in 31.6
seconds. Their temporary source copies were removed after checking. Both delivered Lean
files have zero `sorry`, no debugging options, and lines at most 100 characters. The parent
and public core theorem statements were checked verbatim against their original sources.

## Proved and sorry left

The original module had one hole, in
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_raw_localized_identity_comparison`
(node `lem-sf-integral-adjunction-raw-localization-identity`). Its original arbitrary-R
statement was false and is not claimed as proved. The corrected normalized statement is
proved, and the original existential parent theorem has a complete proof from the actual
localized adjunction. `exists_raw_localized_adjunction_core` remains proved with its original
signature. Holes left in the item: zero. Holes added: zero. Split off: zero.

## No longer needed

Removed the proof import `Sheaf.Paper.SfRationalLocalizationOrthogonality`, associated with
`lem-sf-rational-localization-triangle-orthogonality`. This argument needs no geometric
open/closed operations or orthogonality theorem. Its generic scalar-localization ingredients
are imported directly from `Sheaf.CategoryTheory.SemilinearScalarLocalization` and Mathlib.
The item's public statement-import closure does not otherwise reach the removed module.
This does not withdraw that module or assert that its other consumers no longer need it.

The parent proof no longer depends on the separate core node
`lem-sf-integral-adjunction-raw-localization-core`: it uses the same private normalized
construction while retaining its two normalization properties. The public core theorem stays
in the module as a proved corollary. Removed the private `fullIntegralAdjunction`,
`rawRationalFactor`, and `fullIntegralExact` wrappers. All four generic dependencies previously
listed for the core remain needed. No public declaration or existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous identity-comparison split quantified over every `RawLocalizedAdjunction`, whose
fields do not impose the claimed normalization. Negating the unit and counit of an identity
adjunction on a nonzero characteristic-zero category preserves the adjunction but violates
identity-component compatibility with the original counit. Independently, its left shift need
not match the integral shift. The existing STATEMENT-DISPUTED comment correctly identified
this defect; the previous one-line DAG proof did not resolve it.

The repair is to retain the counit formula and left shift square of the particular
localization construction and then prove the right square by the mate calculation. The
unchanged parent now supplies both facts instead of applying a false arbitrary-R helper.
The zero category and identity operations require no additional hypotheses or nonzero
assumptions: all comparison components are literal identities, and the mate proof uses only
the adjunction laws.

The current server queue lists this item as disputed; its historical build-error record
reports bad dependency imports. The source and Lean attachments were preserved. An initial
unchanged-source compile typechecked but took 77.3 seconds, so profiling and proof-local
simplifications were also necessary. No source-library declaration or launcher tool changed.

## New nodes

`def-sf-integral-adjunction-raw-localization-data` owns the existing literal tensor definitions,
canonical endpoint shifts, RawLocalizedAdjunction record, operation packaging and the proved
identity-component comparison in the new module
`Sheaf.Paper.ExceptionalIntegralAdjunctionLocalizationData`. It introduces no unproved
statement and no mathematical choice. This is a compile-time split after the complete
single-module proof typechecked but exceeded 60 seconds. The associated change record is
`coord/changes/C4-raw-localization-data-module.md`; the other two records are
`coord/changes/C4-raw-tensor-functor-cache.md` and
`coord/changes/C4-normalized-raw-localization.md`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization": "a4c4ba58d7250cba4e53d7a776ace8ac9d97b42a", "Sheaf.Paper.ExceptionalIntegralAdjunctionLocalizationData": "13b75cea3aaa51e4e0f7913667ce2d5cb99f60b1"}, "results": {"Sheaf.Paper.ExceptionalRationalStageLocalization": {"hash": "5a1473e034a5464bde19333cfcaa7507cef91aa2", "status": "OK"}, "Sheaf.Paper.ExceptionalScalarMateLocalization": {"hash": "4ba8b019edebcd4aad254cc002ebb026ebf83c1a", "status": "OK"}}, "seconds": 203, "time": "2026-10-28T01:09:21+0800", "transitive": 1, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
