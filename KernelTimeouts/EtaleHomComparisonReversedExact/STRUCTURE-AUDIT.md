# STRUCTURE EXPOSURE AUDIT

Case: `EtaleHomComparisonReversedExact`
Source snapshot: `8ca2e912b93`, `etaleHomComparison_reversedExact_commShift_component`
Lean/Mathlib: 4.35.0, one Lean thread, normal Kernel checking, 200,000 heartbeats

## R1. Exact Kernel cost site and initial mismatch

The first expensive operation is argument 26 (`hv`) of
`derivedTensorHomShiftComparison_component`, after the preceding concrete
arguments instantiate its dependent binder. The actual term has type
`IsEtaleHomTranspose X φ M v`; the expected type is an instantiated `forall`
over a derived-category object and a transpose equality. Unfolding the named
predicate exposes the first data mismatch: `DerivedCategoryModule A X` versus
raw `DerivedCategory (Sheaf ...)` in the quantified domain. This is a
dependent-domain bundle, not a proof-body mismatch.

The application-only baseline is 29.02 s (about 3.2 s with Kernel skipped);
the full Before is 109.87 s and After is 3.50 s.

## R2. Candidate exposure boundary

The initial heads are an application of `IsEtaleHomTranspose` versus a
`forall`. One source-level unfolding exposes the `forall K` body. The next
boundary is its quantified domain, where the wrapper abbreviation and raw
derived category differ. `TransportHead.lean` verifies the transported lambda
has the exact instantiated expected proposition. No projection occurs on the
first path; the actual Kernel sequence is inferred from source reduction.

## R3. Exposed data-bearing structure

```text
hv : dependent transpose proposition
|- forall K : derived category, evaluation-transpose equality
|  |- DerivedCategoryModule/raw DerivedCategory domain
|  |- scalarExtension and CommShift
|  |- tensor-Hom comparison functors and adjunction data
|  `- v.app and concrete category instances
`- repeated wrapper/raw occurrence in the equality body
```

The prior diagnostic recorded 421,348 `Add.add`, 303,281 `Functor.obj`, and
213,332 `DFunLike.coe` unfolds in the application conversion. Those counters
are direct observations of the probe, not a trace of Kernel decision order.

## R4. Cost distribution and reduction footprint

Predicate-only, raw-domain-only, and all-wrapper partial controls remain
expensive (28.72, 28.92, and 29.12 s). The complete transported `hv` control
takes 3.40 s (2.46 + 1.08 s CPU, 3.18 GB RSS). Thus the hotspot is one
dependent application argument, with repeated wrapper occurrences beneath it;
the full theorem adds later conversions.

## R5. Causal control

`TransportHV.lean` changes only argument 26 to a lambda transporting `hv K`
to the exact expected domain. The same helper application and obligation are
checked with normal Kernel checking, and the pair is verified to change at the
intended binder. The full `After.lean` checks the theorem. Partial wrapper
alignment is a negative control; whole-domain alignment is positive.

## R6. Exposure-footprint comparison

Original: named predicate unfolds into a wrapper/raw quantified domain and
forces conversion under scalar extension, tensor-Hom, and `v.app`; large
`Add.add`/`Functor.obj`/`DFunLike.coe` counts are observed.
Aligned: the dependent proposition is syntactically the expected one; the
same helper application is 3.40 s.
Restored: the original `hv` term in `Before.lean` returns the 29.02 s site.
The exact inner `Functor.comp` child remains unresolved.

## R7. Classification and confidence

Classification: **P2 (dependent bundle-triggered exposure)**, with a repeated
wrapper occurrence beneath the same proposition.
Confidence: **Confirmed** for the whole-domain causal control; **Strongly
supported** for the nested structure mechanism.
Directly measured: exact argument boundary, expression movement, timings, and
unfold counters. Structurally inferred: the reduction boundary and field tree.
Unknown: which `Functor.comp` argument dominates after transport.

## Most important result

The first visible named-predicate mismatch is not enough to explain the cost;
the complete instantiated dependent domain must be aligned. That alignment
removes the application hotspot while preserving the original consumer.
