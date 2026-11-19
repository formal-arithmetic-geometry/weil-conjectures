# KernelTimeouts workplan report

This report covers the assigned Batch B and Batch C cases and
RealPushforward as the necessary-unfolding reference. Each case's
`WORKPLAN-EXPERIMENTS.md` contains the §9 experiment records,
exact localized conversion, structural probe, wall and CPU times,
peak RSS, and confidence limits. The separate
`WORKPLAN-MATRIX.md` uses the exact six columns of §7.1.

## Protocol

The source snapshots and declaration contexts are those of the
existing Head Audit. New variants changed one corresponding
argument, representation kind, or instance path at a time,
except for labeled pair/combined controls. After each source
edit, a structural probe checked the resulting elaborated pair;
unchanged-pair edits are not credited with causal effects.
The same application-domain, final-type, or explicit
`change` conversion was remeasured. Runs used Lean/Mathlib
4.35.0 in the prebuilt master environment, one Lean process
and one Lean thread at a time, `timeout 3600`, and
`/usr/bin/time -v`. A baseline was rerun when comparing
across measurement sessions. Normal Kernel checking is
required for successful controls; a diagnostic `sorry`
after the audited application and a Kernel-skipped phase
probe are identified explicitly in the case records.

## Case outcomes

The **Observed** column reports checks and expression changes.
The **Interpretation** column states the mechanism inferred
from those observations. Confidence refers to that
interpretation, not simply to the existence of the hotspot.

| Case | Experiments | Observed | Interpretation | Confidence |
|---|---|---|---|---|
| [OrderedSpectralRawLattices](OrderedSpectralRawLattices/WORKPLAN-EXPERIMENTS.md) | C1-R/H/D, C1-RH/RD/HD, C1-RHD | Every single and pair instance-availability control times out. Disabling both local-ring paths moves the first mismatch to a domain instance. Disabling all three aligns both ring-object let values and the declaration checks. | The concrete local-ring and domain routes interact; none of the three changes alone suffices. The final predicate wrapper remains but is cheap in the aligned setting. | **Confirmed** for the three-path interaction; exact Kernel order unresolved. |
| [EtaleHomComparisonReversedExact](EtaleHomComparisonReversedExact/WORKPLAN-EXPERIMENTS.md) | B1-P/D/W/T | Expanding the predicate, then only the binder, then all derived-category wrappers leaves the application expensive. The first nonproof difference progresses to `EtaleHomLeft` versus `Functor.comp`. An argument at the exact expected proposition checks cheaply. | This is a multilevel dependent proposition mismatch. Predicate exposure is necessary; wrapper alignment alone is insufficient. | **Confirmed** for exact-proposition alignment and the negative wrapper controls; causal functor argument unresolved. |
| [FiniteBaseChangeRestrictionMateTransport](FiniteBaseChangeRestrictionMateTransport/WORKPLAN-EXPERIMENTS.md) | B2-S/T and site-unfold diagnostic | The ordinary `Site` type reduces to `ProEt`. Replacing those stored site types exposes a distinct category-instance argument. Transporting only proof argument 49 to the exact expected proposition turns a Kernel timeout into success. | The dependent site representation is an entry point, followed by a mode-specific category instance; whole-proposition alignment avoids their expensive comparison. | **Confirmed** for the transport control; individual site and instance shares remain **plausible**. |
| [F66Adj](F66Adj/WORKPLAN-EXPERIMENTS.md) | B3-L/R/Q | The over-object's left field reduces to the local scheme. Replacing only proof argument 39 removes that first stored difference and the helper-application cost; a preceding tensor-isomorphism change does not. | The supplied proof proposition's concrete over-object representation creates an unfavorable path. The one-argument replacement changes the proof-producing interface as well. | **Confirmed** for argument-39 representation; accessor leaf alone **strongly supported**, not isolated. |
| [ImageHomCounit](ImageHomCounit/WORKPLAN-EXPERIMENTS.md) | C2-W/I | Unfolding only the target wrapper changes the elaborated pair but makes the checked final conversion slower; another nested wrapper/raw difference remains. Using the unchanged proof term's exact inferred target makes the pair syntactically equal and the check cheap. | The first wrapper is necessary to expose, but the cost belongs to a deeper representation comparison. Full endpoint alignment avoids it. | **Confirmed** for full alignment and failure of wrapper-only sufficiency; dominant nested child unresolved. |
| [IntegralComparisonPullbackRealizationShifts](IntegralComparisonPullbackRealizationShifts/WORKPLAN-EXPERIMENTS.md) | C3-I/K | Aligning the actual stored `HasDerivedCategory` instance moves the first difference to `FullSubcategory` versus `CochainComplex`, yet costs essentially the same. The edited probe is fast with Kernel checking skipped. | The instance leaf is a first visible mismatch, not a sufficient explanation. The cost remains Kernel-bound deeper in a functor-object conversion. | **Confirmed negative** result for instance-leaf sufficiency; deeper cause **plausible**. |
| [RealPurity](RealPurity/WORKPLAN-EXPERIMENTS.md) | C4-L/R/B | Left, right, and combined ring-instance alignments all change the intended elaborated leaves and all still time out. The next difference on both sides is `Functor.obj` versus local `P`. Head-only probes are fast without `exact h`. | The ring inheritance paths are not sufficient; the final proof-proposition comparison has a deeper concrete object mismatch. | **Confirmed negative** result for ring-leaf sufficiency; object path **plausible**. |
| [RealPushforward](RealPushforward/WORKPLAN-EXPERIMENTS.md) | RP-REF | The original final conversion times out. The one-step `localPolynomial` body exposes `charpolyRev`; the aligned polynomial goal checks while a smaller instance difference remains. | The original representation requires an initial polynomial-definition reduction. Alignment at that level avoids the expensive path. | **Confirmed** representation trigger; downstream sequence unresolved. |

## Cross-case reading

**Observations.** The three dependent proof-argument cases
have expensive instantiated proposition comparisons, and
controls that supply the argument at an aligned proposition
make the same application cheap. EtaleHom retains cost
after wrapper-only alignment. ImageHomCounit also retains
cost after its first wrapper is expanded. IntegralComparison
and RealPurity retain cost after their first concrete
instance leaves are aligned. RealPushforward's two
different regular polynomial heads have a direct
one-step definition relationship.

**Interpretation.** The recurring mechanism is a
representation difference in an actual argument or
dependent proposition that prevents a cheap high-level
comparison. The first unequal leaf is a useful location,
but C3 and C4 demonstrate that it need not be sufficient
to explain the cost. Concrete instances and wrappers can
expose later functor/object differences. RealPushforward
remains the distinct reference where initial unfolding
is necessary for the original named polynomial.
Unfold counters and source notation alone are not used
as evidence of the Kernel's internal order.

**Open causal children.** The next corresponding
`Functor.comp` argument in EtaleHom, the category-instance
path in FiniteBaseChange, the isolated `Over.left` share
in F66Adj, the nested endpoint in ImageHomCounit, the
functor-object argument in IntegralComparison, and the
object argument in RealPurity remain unresolved at a
single-child causal level. These are explicit limits of
the reported confidence, not claims of a completed
internal Kernel trace.
