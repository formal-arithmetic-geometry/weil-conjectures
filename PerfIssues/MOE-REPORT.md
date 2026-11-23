# Mismatch Origin Audit: Seven Cases

This report uses the seven `EXPERIMENTS-MOE.md` case records and their saved
Expr snapshots, source controls, and READY4/READY4.2 Kernel counters. The
case-specific audit notes qualify claims that the snapshots cannot establish.
"Earliest" below means the earliest *supported* checkpoint for the named
difference. A source choice can be visible at S0 while its inferred provider
term first exists at S2. S4 is authoritative for a stored Kernel input.

Historical P1/P7 use Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Current P2-P6
use Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and the
reserved source tree `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`;
individual source revisions are in the case reports. Imported S3 records are
finalization-observable-only, not independent pre-finalization snapshots.

## Cross-case inventory

| Case | Earliest supported difference and provenance | Elaborator contribution | Finalization | Kernel-exposed latent part | Cheap boundary and E3 puncture |
| --- | --- | --- | --- | --- | --- |
| P1 Slow Derived Tensor | S4/S5 exact `tensorObj` argument-2 provider split; source-authored `abbrev`/regular hint variant | No changed S2 output demonstrated | S2/S4 comparison unavailable | `abbrev` exposure enters the 1,785/11,973-node provider arguments | A2 `@[reducible] def` consumer 2/2 ms; type-correct A0 `abbrev` restores 119,953/127,832 ms. Historical A3 body exposure was not remeasured. |
| P2 OrderedSpectral | S0 route availability/API; concrete `Semifield.toCommSemiring` versus `CommRing.toCommSemiring` at S2, helper side import-frozen | Inferred terms observed; causal elaborator effect **not demonstrated** by the source route rewrite | No captured helper pre-finalization Expr | Provider M0 propagates into dependent `Exists`/`Quiver.Hom`/`Functor.obj` | All-route alignment succeeds; restoring one R/H/D route is type-correct and restores the timeout in the saved matrix. `continuousMapRingObj` and whole-side helper are fragile. |
| P3 FiniteBaseChange | S0 `Scheme.ProEt` versus mode-indexed `Site`; S2 `root/fn` confirms | No changed assignment; unification hint leaves pair/counters fixed | Not earliest; imported S3 observational | `Site` delta/mode matcher and category continuation under `hb`; M1 72.869% time | Whole-`hb` transport 19,783 threshold-zero calls; restoring concrete `h` gives 239,340,712 calls. |
| P4 EtaleHom | S0/S1 named `IsEtaleHomTranspose` versus expanded helper domain; S2 root `app`/`forall` | Provider assignments and selected names observed; no alternative selection changes root | Not earliest; imported S3 observational | Predicate unfold exposes `DerivedCategoryModule`/raw domain; M1 99.762% comparison time | Transport 7,039 calls; direct `hv` restores 3,180,470 (expanded domain: 3,179,834). |
| P5 F66Adj | S0/S1 explicit `Over.mk f.left`; S2 proposition has `Over.left (Over.mk f.left)` versus `X` | No competing choice observed | Not earliest; S2/S4 change unmeasured | `Over.left`/dependent category and functor bodies; M1 99.791% comparison time | Direct `restriction_counit` 3.30 s; original image restriction puncture 34.42 s; `tau_q`-only negative control 34.62 s. |
| P6 PR1627 | S0 direct `homMk` API; exact `homMk` versus `CategoryStruct.id` first **verified at S4** in `_proof_2` | Implicit argument refinement plausible; independent causal effect unproved | `_proof_*` generated; whether exact pair arose at S2 or finalization unknown | Dependent law-field domain and proof/data types reach M1/M2; root 10,904,899 calls | `liftOfStr` helper has no >100 ms law-field root; type-correct direct `IsoAlgebra.mk`/`homMk` restores it. |
| P7 Derived-Completion Cone | S0/S1 inline versus named *control*; S2 `root/arg/arg` app/fvar compares variants. Original M0 has 36 differing proof positions at S4 | Inline monoidal synthesis observed; no section-11 causal demonstration | `abstractNestedProofs` generated proof constants materially affect the value-side Expr; exact pre-finalization pair unavailable | Concrete provider/proof proposition descendants; M1 99.694% time | Named `derivedCompletionDiagram` regular head is cheap; type-correct inline use restores 12,220,822 calls. |
| P7 wrapper M/L controls | S0 wrapper vocabulary `M(f)` versus raw `L(f)`/compositors | No independent inference change established | No relevant comparison | Named `Functor.obj`/`Functor.map` heads keep descendants compact | Non-identity wrapper controls stay below timer resolution; raw-vocabulary puncture for the original cone root remains untested. |

The P1/S4 and P6/S4 entries are evidence bounds, not assertions that no
earlier difference exists. P2's inferred provider terms are real S2 Exprs,
but its successful control changes source instance availability. P7's named
control changes source spelling and explicit sharing adds a binder. Its S2
app/fvar path is not the original inline M0's first unequal node. Neither
meets MOE section 11's causal Elaborator test. In P4 the trace *does* select
specific provider names; what is missing is an alternative selected provider
that changes the final root and frozen cost.

## Targeted Batch 2 results

The only concrete decision sites warranting provider/transparency trials were
P2's R/H/D instance routes, P4's argument-26 domain constraint, and P7's
monoidal provider. P2's all-disabled and partial-restoration matrix changes
source instance scope and S2 ring-object providers, but saves no independent
assignment-level F0/F1 replay. P4's fresh Meta trials give `false` for
`none`/`reducible`/`instances` and `true` for `default`/`all`; no successful
trial selects a different final Expr. P7's explicit provider control changes
the dependent telescope, so it cannot isolate the original M0. No broad
transparency sweep is interpreted as causal evidence.

P4 has a same-context frozen-expression replay (`moe/P4Frozen.lean`): F0
direct `hv` has unequal actual/expected Expr hashes and READY4.2 root 2749
uses 3,180,439 calls; F1 transported premise has identical Expr hashes and
root 2750 uses one call. Both checks succeed in the same Environment and
local context. The source changes the supplied premise, so this establishes
an expression-level boundary effect, not an Elaborator-only perturbation.
The separate same-consumer source controls give 3,180,470 versus 7,039 calls.
No strict F0/F1 replay with independently frozen changed metavariable
assignments is available for P2 or P7; no F2 same-Expr metadata-only replay
was constructed.
For P6, an S2 generated-law snapshot is missing. The nine type binders versus
eight value binders in stored `_proof_2` identify an S4 asymmetry, not a
proven S2-to-S4 transformation. The exact pair's finalization origin remains
open. The case audit notes record one type-correct E3 puncture per P1-P7;
these reuse the saved, measured controls rather than claiming new timings.

## Answers to the research questions

1. **Earliest stages.** Source/API differences are supported at S0/S1 in
   P3-P5 and P7. P2 has source route availability at S0 and concrete inferred
   provider terms at S2. P1's exact provider pair is verified at S4/S5. P6's
   exact generated-law pair is verified at S4, with its `homMk` source choice
   visible at S0. P7's original inline M0 proof positions are verified after
   proof abstraction at S4; the named-control difference starts at S0.
2. **Origins.** P1's declaration-kind control is source metadata plus Kernel
   strategy. P2 combines source instance scope, inferred terms, and an
   import-frozen helper. P3-P5 and P7 start from source/API representations.
   P6's generated opaque proofs are finalization products, but the first
   exact pair is not proven to be finalization-generated. P7's generated
   proof constants materially change the inferred/value side; no saved S2
   original law Expr pins their first appearance. Kernel exposure
   amplifies latent bodies in every expensive root; it does not create the
   written choices.
3. **Elaboration.** Instance synthesis and implicit arguments materialize
   concrete terms in P2/P4/P6/P7. P4's relevant constraint needs Meta
   `default` or `all`. No case currently satisfies section 11's stronger
   demonstration that an Elaborator-only change altered assignments, final
   Expr, and frozen Kernel cost. No first-path coercion insertion is isolated.
4. **Fragile cheap boundaries.** The measured punctures identify a regular
   head (P1), route-aligned data heads (P2), whole-premise transports (P3/P4),
   a direct restriction proposition (P5), a generic helper (P6), and a named
   diagram (P7). They are maintenance risks when consumers unfold bodies,
   rebuild proofs, restore independent providers, or mix raw vocabulary.
5. **Upstream choices to M1.** The strongest traceable links are P3's
   `ProEt`/`Site` pair to 239,340,712 calls, P4's predicate/domain pair to
   3,180,470 calls, P5's over-object proposition to 3,897,905 calls, P6's
   direct law construction to 10,904,899 calls, and P7's inline diagram to
   12,220,822 calls. Restoration controls re-enter these paths. The counters
   do not apportion every M1 descendant to one leaf.
6. **Negative controls.** P1's unchanged tensor argument cost under the
   declaration-kind control argues against an S2 speedup. P3's unification
   hint leaves the pair and counters unchanged. P4's lower transparency modes
   fail and its successful modes do not change the final Expr. P5's `tau_q`
   edit leaves the slow cost. P6 `_proof_3` has no corresponding structural
   argument difference. P7 wrapper M/L controls are cheap non-identity
   conversions; P2 partial route removals remain expensive. These limit
   Elaborator and one-leaf explanations rather than proving global absence.

The common mechanism is a concrete upstream representation difference that
enters an S5 conversion, then survives recursive comparison as M1/M2. The
origin differs by case. Timing alone is not used to assign provenance; the
named Expr paths, source forms, stored hints, and restoration controls carry
the claims above.
