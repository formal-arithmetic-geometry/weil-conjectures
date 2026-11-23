# CCMOA: PR2122 finite-etale integral boundary

Case: PerfIssues/Old/PR2122-DiagonalTraceFiniteEtaleIntegralBoundary

## Scope and provenance

This is the P7 historical control. The existing anatomy, branch audit, IM,
and READY4.2 M1 records were reused. Raw facts are in ccmoa/pr2122-snapshot.txt.
The original theorem source is Before.lean. No standalone dependent branch
was extracted.

## Experiment A: lightweight stage audit

| Stage | Snapshot |
| --- | --- |
| S0 | The source theorem has 14 binders and 12 lets. The source obtain pattern `obtain <alpha,beta',halpha,hbeta,hN> := hc P n` elaborates to a dependent Exists recursor. The source also contains concrete category/functor/ring constructions named in the historical diagnosis. |
| S1 | No macro-expanded syntax snapshot was retained. The source obtain is the only recorded syntax boundary. |
| S2 | Unknown. The original replay cannot currently load the required GmRelativeKummer compiled module, and no valid pre-finalization Expr was saved. |
| S3 | Unknown. No pre-finalization declaration term is available. |
| S4 | Valid stored-value inspection instantiates all 14 binders and 12 lets, then sees terminal const Exists.casesOn with five arguments. The full value replay is about 172.014 s; the final inferred/declared conversion is about 1 ms. The first raw type diff is an Expr.mdata wrapper versus Eq, which is not a causal mismatch. |
| S5 | The valid original recursor context has READY4.2 root 35261. It performs 2257184 calls; M1 is 1797805 calls and 98.113 percent of exclusive time. The exact inner actual/expected Expr pair at the first divergence was not serialized. |
| S6 | The motive and witness/predicate checks are valid in the instantiated context (16115 ms and 18419 ms; witness body 2212 ms). The final branch cannot be checked independently because its expected type is supplied by the dependent motive. No first reduction or projection exposing a concrete mismatch was isolated. |

The earliest exact mismatch stage is therefore Unknown. S4/S5 establish the
dependent recursor boundary and the Kernel workload, but not the first
divergent child.

## Experiment A validity and controls

The required lightweight A was not run as a claimed replay. The current
read-only closure is missing GmRelativeKummer.olean, and the only permitted
branch-local replay is the original Exists.casesOn motive/witness context.
Extracting the final branch or replacing it changes the motive and is not a
type-correct control for the original root.

The existing MatchedGeneric diagnostic compares an Exists.casesOn body with
an id-wrapped body. It has heads Exists.casesOn/id, two calls, depth 1, and
0.038 ms, but it does not preserve the original dependent telescope. It is
recorded as a negative diagnostic only, not as a causal A or B result.

No valid B control exists in the saved artifacts. The broad aligned module
changes imports and theorem construction, so its 5.142 s / 510125-call
measurement is not a one-factor representation control. No counter
before/after pair is assigned to it.

## Experiments C and D

C: Unknown. S2 is unavailable, and extracting a branch to trace motive or
implicit assignments is invalid. The READY4.2 M1 table is a workload
classification, not an elaborator provenance trace.

D: Unknown. The stored declaration can be inspected, but the pre-finalization
term and any generated proof declaration that could change this pair were not
captured.

## Experiment E: boundary inventory

| Boundary | Current behavior | Puncture | Status |
| --- | --- | --- | --- |
| Exists.casesOn motive/witness/final branch interface | The motive and witness are independently checkable only after all theorem binders and lets are instantiated; the final branch type depends on both. | Standalone extraction or branch replacement changes the root obligation and fails validity. | Fragile but effective as a validity boundary; not a cheap conversion boundary |
| Concrete category/functor/ring data inside the recursor | Historical source identifies DiagonalAb versus sheaf categories, functor composition forms, and ring instance forms, but no exact inner pair is stored. | No type-preserving puncture is available without the original replay closure. | Untested |
| MatchedGeneric Exists.casesOn/id diagnostic | The surrogate is below timer resolution (0.038 ms) because it has a tiny non-dependent body. | Restoring the original motive/witness context removes the surrogate shortcut; no paired original replay is available in this closure. | Not actually responsible for the historical cost |

## Synthesis

| Case | Earliest divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| PR2122 | Unknown | Plausible source/API representation bundle exposed in a dependent Kernel check | Unknown | Unknown | Plausible | Exists.casesOn dependent telescope | Fragile but effective |

The Kernel phase and M1 dominance are demonstrated. The source-level
representation candidates and the connection to the measured inner pair remain
Plausible because no valid one-factor replay preserves the original motive,
witness, and branch context.
