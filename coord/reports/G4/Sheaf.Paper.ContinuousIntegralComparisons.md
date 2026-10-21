## What changed

Restored lean/Sheaf/Paper/ContinuousIntegralComparisons.lean from its authoritative
quarantine archive, as assigned by coord/rework.tsv. All six real constructions are retained:
integralScalarConstructible, integralConstructiblePullIso, integralConstructiblePullHom,
integralConstructiblePushHom, integralConstructibleSourceHom and integralConstructibleTargetHom
(in AlgebraicGeometry.ProEtale.CondensedRing). Only whitespace differs from the archive,
to satisfy the 100-character line limit. The restored module compiles in 10.9 seconds with
no errors or warnings. No public signature, definition body, import or instance changes.

The repair restores definitions at a missing live path; it is not a proof-only no-op or
withdrawal. Record: coord/changes/G4-restore-continuous-integral-comparisons.md.
The assigned DAG attachment and all dependencies are preserved. Six DAG parents and five
archived direct importers were checked; no consumer source needs adapting.

## Proved and sorry left

Zero original sorry proofs; zero closed; zero added; zero remaining; zero split off.
This is a zero-hole definition restoration, not a claimed proof gain.
The six definitions above retain their existing complete bodies. Their boundedness and
functor-law proofs are complete; no definition contains sorry or arbitrary witness data.

## No longer needed

None. No imports, declarations, modules or DAG dependencies are removed. The absence of
live consumers does not justify withdrawal: the six retained DAG parents and quarantined
consumer sources still need these comparisons. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with sorry, but the current assignment is a
quarantined zero-hole definition module. The row records a reverted cluster restoration,
not a mathematical flaw. Its archive compiles unchanged except for inherited long-line
warnings, repaired here by wrapping whitespace. No false statement or new lemma was needed.
Mathlib full-subcategory infrastructure and the library canonical comparison definitions
already provide exactly the required constructions.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
