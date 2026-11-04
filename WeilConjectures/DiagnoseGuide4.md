# Lean 4 Kernel Performance — Continuation Diagnostic for a Transparent Wrapper API

**Status:** Investigation plan; **no new final solution is established yet**.  
**Target:** The `moduleObjectDerivedPullback` interface, its composition/identity isomorphisms, and the coherence proofs reproduced in `WeilConjectures/Reproducer.lean`.  
**Known working fallback:** The original-statement-preserving, ordinary-kernel-checked component proof in `ReproduceFixed.lean` (Report 2).  
**Immediate research question:** Does the Report 3 speedup come primarily from a **uniform wrapper-vocabulary API**, or is hiding / restricting the wrapper definition actually necessary?  
**Preferred outcome:** A maintainable **ordinary transparent `def`** API with acceptable performance. This is a hypothesis to test, **not** a predetermined result.

This document is an executable assignment for a local coding agent. Read the actual Lean declarations, available scratch experiments, and local reports before implementing any schematic code below. You may consult the version-matched Lean/Mathlib implementation online when needed, but measured local evidence takes precedence. Do not modify the general performance guide or claim an architectural solution until this investigation has a checked result.

## 0. Constraints and what counts as success

1. **No opacity in a final repair.** Do not introduce the Lean `opaque` declaration, `@[no_expose]`, or a new `@[irreducible]` declaration/attribute in committed repair code. These may appear in **isolated diagnostic controls only**, never in the final patch or its required API modules. Do not reinterpret an imported hidden definition as a transparent repair.
2. **Ordinary kernel checking is mandatory.** No new `sorry`, `sorryAx`, axioms, `debug.skipKernelTC`, weakened checker settings, or heartbeat increases as the final solution. Scratch-only placeholders and kernel-skipped comparisons are allowed only to localize a cost.
3. **`HEq` may be used to diagnose conversion**, including controlled self/cross probes, but must not appear in the final repair's new theorem statements, proof construction, or helper APIs. Prefer ordinary `Eq` and high-level structural lemmas in production.
4. **Do not silently change public statements.** Distinguish two acceptance tracks:
   - **Track P — original-statement preserving:** `repro_exact_elab_timeout` and `repro_congr_kernel_timeout` keep their original upstream-compositor vocabulary and the same elaborated types. This is the default compatibility requirement and is already met by the Report 2 repair.
   - **Track A — canonical-API experiment:** the local reproducer statements may temporarily use `moduleObjectDerivedPullbackComp/Id` to measure a proposed internal API. This is **not equivalent to Track P**; any production-facing statement change requires a separate compatibility and downstream decision.
5. **Do not change multiple experimental axes at once.** Preserve a clean worktree, exact source snapshot, logs, toolchain revision, and one hypothesis per named variant.
6. **Count all work**, including new compositor definitions, coherence helpers, imported API modules, auxiliary proofs, elaboration, kernel checking, CPU time, and peak RSS. A slow check shifted to a helper or new module is not an eliminated cost.
7. **Do not start a repository-wide migration.** Report 3 identifies roughly 61 users of the wrapper, including files that explicitly `unfold` or `delta` it. First establish the smallest reliable local comparison.
8. **Keep the already verified Report 2 repair available as the fallback.** An attractive but unverified API refactor must not replace the checked, original-statement-preserving solution.

## 1. Evidence already available: established facts versus open hypotheses

### 1.1 What the previous reports actually establish

| Observation | Evidence | Permitted conclusion |
|---|---|---|
| The original mixed-vocabulary proof times out | Original `exact h2` elaboration failure and `congr 1` kernel failure | A costly conversion is exposed by the mixed expressions |
| The hotspot lies under a composite natural-isomorphism component | Report 1: `type.2.5`, `NatTrans.app` applied to a composite; individual arguments cheap, full conversion expensive | Projection-level cross-expression conversion is dangerous |
| A **regular-def wrapper plus aligned compositor types** can already work in one design | Report 1 X6: `dncComp/dncId`, coherence helpers, changed statements, ordinary kernel success | Opacity is **not a general prerequisite** for a normalized-vocabulary theorem |
| The original theorem statements can be kept unchanged | Report 2 Y4: abstract component lemmas and an `Eq.trans` chain, ~3 s kernel per repro theorem | There is a verified production-compatible fallback without opacity |
| Rewriting concrete composite expressions can be costly by itself | Report 2 Y1/Y1a/Y2/Y3a; Y1a remains kernel-slow after the final `exact` is sorried | Do not rely on goal-side `simp`/`rw` as the next default fix |
| Removing the wrapper syntactically is not a free simplification | Report 3 `v_nowrap`: all three statements fail elaboration around `congrArg` lambdas and `.leftDerivedFunctor` | The ordinary named boundary has real elaboration value in the tested shape |
| Moving an unmodified wrapper across a module boundary does not help alone | Report 3 `v_imp_plain` | Module placement alone does not solve mixed-vocabulary checking |
| Changing only to `abbrev` or `@[reducible] def` does not help | Report 3 `v_abbrev` / `v_red` | Simple reducibility changes are not the fix in the original mixed setting |
| Hiding the wrapper **without normalizing consumers** produces type errors | Report 3 `v_imp_noexpose` | The original statements rely on cross-vocabulary definitional equality |
| Uniform wrapper API **plus** `irreducible` or `no_expose` works | Report 3 `v_irr` / `v_nx`, using changed statements but original short proofs | Those **combinations** work; they do **not** isolate the contribution of opacity |

Do **not** flatten these into a claim that `no_expose` is required or that transparent `def` must fail. Also do **not** claim that the Report 1 X6 control is exactly equivalent to the Report 3 successful variant: its helper set, exact declaration layout, and proof architecture differ.

### 1.2 The unresolved comparison

The most informative missing experiment is:

> **Take Report 3's working `v_irr` variant, remove only `attribute [irreducible] moduleObjectDerivedPullback`, and keep the entire canonical API, its theorem statements, proof scripts, and module layout unchanged.**

This is the **Transparent Canonical API** control. It must be performed before interpreting the `no_expose` result as evidence that an abstraction barrier is necessary for speed.

The competing hypotheses are:

- **H1 — vocabulary consistency is sufficient:** the wrapper and its compositors use one regular-`def`-based API; the original short proofs work without opacity.
- **H2 — elaborator transparency still matters:** even with the API aligned, removing `[irreducible]` causes a specific elaboration conversion, typeclass search, or expression-building regression.
- **H3 — kernel conversion remains costly:** aligned types elaborate, but some checked proof application still triggers a costly conversion under the transparent definition.
- **H4 — module placement, imports, or generated proof sharing confound the measurement:** a same-file control and an imported-API control behave differently despite identical public declarations.
- **H5 — changed theorem vocabulary is the decisive relaxation:** the canonical API is fast, but retaining the original `leftDerivedUpperStarComp/Id` statement necessarily requires a different proof boundary (such as Report 2 Y4).

The first job is to **discriminate**, not to choose a favorite hypothesis.

## 2. Prepare a controlled experiment workspace

1. Save `git rev-parse HEAD`, `lake env lean --version`, Mathlib revision, hardware/load, `lakefile` options, and any project-local `set_option` declarations. The report environment was Lean/Mathlib **4.33.1** on `slopmaster2` at approximately `55376e1a60`; verify the actual worktree instead of assuming it is unchanged.
2. Locate the real Report 3 scratch variants (`wrap/`, `nx/ScratchNX/`, runner scripts) if they are still present. Do not reconstruct the successful `v_irr` from memory if its exact source is available.
3. Preserve three immutable controls:
   - **P0:** the Report 2 `ReproduceFixed.lean` proof with original statements;
   - **M0:** the original mixed-vocabulary reproducer and its known failures;
   - **Aopaque-control:** Report 3's successful `v_irr` or `v_nx` source (diagnostic only, never a final candidate).
4. Create an **Atransparent** copy from the successful `v_irr` source. Remove **only** the `attribute [irreducible]` line. Check for other local/scoped transparency attributes, hidden imports, or implicit wrappers which would invalidate the control.
5. Run one Lean process at a time on the shared host. Keep complete stdout/stderr and exact source diffs.

Illustrative options from the reports, subject to project-local verification:

```bash
lake env lean --version
/usr/bin/time -v timeout 240 lake env lean \
  -DElab.async=false \
  -Ddebug.skipKernelTC=false \
  -Dpp.unicode.fun=true \
  -DrelaxedAutoImplicit=false \
  -Dbackward.isDefEq.respectTransparency=false \
  -DmaxSynthPendingDepth=3 \
  -Dwarn.sorry=false \
  -Dlinter.style.longLine=false \
  scratch/transparent_candidate.lean \
  > scratch/transparent_candidate.log 2>&1
```

Use the appropriate `time` executable if `/usr/bin/time` does not exist on this machine. Keep profiler-on and profiler-off measurements separate. A `timeout` is an experiment ceiling, not a way to declare a theorem repaired.

## 3. The minimal comparison matrix

**Run these variants in order.** Names are new for this investigation; no historical numbering is required.

| Variant | Wrapper | Consumer vocabulary | Module layout | Proof structure | Role |
|---|---|---|---|---|---|
| **P0 — checked fallback** | existing regular `def` | original upstream `leftDerivedUpperStarComp/Id` | current Report 2 layout | abstract components + `Eq.trans` | Original-statement baseline |
| **A1 — transparent canonical** | ordinary `def`, no opacity attributes | `moduleObjectDerivedPullbackComp/Id` + wrapper-typed coherence lemmas | same file as `v_irr` | original `exact h2` / `congr 1` | **Primary missing control** |
| **A2 — transparent imported API** | ordinary imported `def`, no opacity attributes | same as A1 | separate API module imported normally | same as A1 | Isolate module placement / API build costs |
| **A3 — irreducible diagnostic** | same `def`, plus local `[irreducible]` | same as A1 | identical to A1 | same as A1 | Reproduce Report 3 positive control; **never ship** |
| **A4 — no-expose diagnostic** | real `@[no_expose]` module boundary | same canonical vocabulary | defining module + normal importer | same as A1 | Reproduce Report 3 public-view control; **never ship** |
| **M0 — mixed negative** | ordinary `def` | wrapper mixed with upstream compositors | controlled original layout | old failing proof | Confirm old symptom if needed |
| **P1 — compatible integration** | ordinary `def` | **original** theorem statements | as small as feasible | A1 helpers internally or Report 2 components | Test public compatibility, distinct from A1 |

### Critical discipline

- **A1 versus A3** isolates the effect of `attribute [irreducible]` while keeping the canonical API fixed.
- **A1 versus A2** isolates module placement while keeping both transparency and vocabulary fixed.
- **A2 versus A4** is informative **only** if public declaration types, imported visibility, and consumer expressions are appropriately controlled. Actual `no_expose` changes which conversions are legal, so a raw timing comparison is not by itself causal proof.
- **A1 versus P0** is **not** an apples-to-apples performance comparison: P0 preserves upstream theorem statements and has additional component helpers; A1 changes vocabulary and uses shorter proofs.
- Existing X6 from Report 1 provides an important positive precedent for ordinary `def` + a normalized API, but does not replace the exact A1 experiment.

Do not run the full factorial product of every variable without a reason. A1 is the highest-information next action.

## 4. Exact implementation for A1: ordinary transparent canonical API

Adapt the **actual** Report 3 successful variant; the following is schematic to document the intended invariant, not copy-paste-ready Lean code.

```lean
-- Keep the existing regular definition as a normal `def`.
-- Do not add `opaque`, `@[no_expose]`, or `[irreducible]`.
def moduleObjectDerivedPullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) : ... :=
  (upperStar Λ f).leftDerivedFunctor

-- A canonical compositor interface whose *declared type* uses the wrapper.
def moduleObjectDerivedPullbackComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleObjectDerivedPullback Λ (f ≫ g) ≅
      moduleObjectDerivedPullback Λ g ⋙
        moduleObjectDerivedPullback Λ f :=
  leftDerivedUpperStarComp Λ f g

-- Likewise use the wrapper vocabulary in Id and coherence statements.
-- Verify the real binder types and available upstream lemma names.
```

The key experiment is **not** just making the wrapper transparent. The entire tested theorem's **compositor values, implicit functor arguments, and coherence lemma statements** must be built in the canonical wrapper vocabulary, just as in the Report 3 working consumer.

For A1, retain the exact short proof scripts used in the positive control. In particular, do not silently swap `congr 1` for the Report 2 `Eq.trans` proof, because that would confound the experiment.

Optional `moduleObjectDerivedPullback_eq` may be included as a separate API experiment. With an ordinary transparent `def`, measure a direct `rfl` or an explicit local unfolding proof. **Do not use this equality lemma to rewrite the large concrete goal** as part of A1; that would test an entirely different mechanism.

### Verify the variant's actual semantic contract

Record:

1. The precise declared type of `moduleObjectDerivedPullbackComp/Id`.
2. Whether all wrapper-vocabulary associativity and unit lemmas have the intended types.
3. Whether `dncPullbackComp_congr_left/right` still check without expensive hidden conversions.
4. Whether the consumer statements actually changed from the original upstream vocabulary.
5. Whether `exact h2` / `congr 1` are unchanged and the elaborated proof terms pass normal checking.

Do not report A1 as a repair of the unchanged public theorem unless point 4 confirms unchanged theorem types—which the Report 3 design does **not** predict.

## 5. Interpret A1 by *phase*, not just by success or failure

### Outcome A — A1 succeeds with ordinary transparent definitions

This would establish that **opacity is unnecessary for the Report 3 canonical-vocabulary reproducer**. Next:

1. Repeat A1 at least three times and collect per-declaration kernel times.
2. Compare with A3 under the same measurement conditions; avoid treating small wall-time differences as meaningful on the overloaded host.
3. Test A2 to see whether a plain imported API remains fast and whether its compilation costs are reusable/amortized.
4. Remove any diagnostic settings and check axioms; confirm all API/helper declarations are regular public `def`/theorem declarations.
5. **Do not immediately migrate the 61 downstream files.** First try a small importer that uses the canonical wrapper API and identify any deliberate dependence on direct unfolding.
6. Decide separately whether Track P is needed. A1 alone does not give the original theorem statement back.

### Outcome B — A1 fails during elaboration, while A3 succeeds

Opacity/irreducibility may be influencing elaborator decisions. Locate the **first exact elaboration action** that diverges:

- declaration signature elaboration, instance synthesis, or elaboration of a `congrArg (fun f => ...)` lambda;
- synthesis of implicit functor arguments for an upstream compositor;
- matching the actual argument type to the expected dependent binder domain;
- `exact h2` / `rw` / `congr 1` or generated proof abstraction.

Run a typed, minimal control with the same inferred parameter types. Use the actual binder domain and stored `Expr` when printed types appear equal. If a comparison is cheap with named `def` heads but slow after unfolding, introduce an **ordinary named interface** at the highest useful level rather than keeping `[irreducible]` in the final code.

Possible transparent repairs to test **one at a time**:

- assign explicit functor parameters at the application site;
- provide exact binder types and types for dependent lambdas instead of leaving object/scheme types unresolved;
- replace an unnecessarily exposed expression with a regular `def` whose arguments are cheap to compare;
- use a small, precisely typed bridge theorem at a high level, *before* `NatTrans.app` / `Functor.map` projection;
- use the Report 2 abstract component lemma pattern when no cheap direct application exists.

Do not infer that opacity is necessary merely because one elaboration tactic times out.

### Outcome C — A1 elaborates but kernel-checking remains slow

Investigate **where** the kernel pays:

1. Profile each declaration, including `moduleObjectDerivedPullbackComp/Id`, coherence helpers, generated auxiliary theorems, and the consumer theorem.
2. Compare the declared type, the inferred value type, and the smallest application domains involved in the slow proof term.
3. Preserve the exact `NatTrans.app` / `Functor.map` application and its hidden `F`/`G` arguments in a structural diff; do not rely on pretty-printed equality.
4. If appropriate, use separate diagnostic `HEq` P1–P5 controls to tell ordinary term checking from expensive cross-expression conversion. **Delete them before finalizing.**
5. Check whether the new API merely moved the same reduction into a helper or imported module.
6. If the expensive term is still a composite projection, try the Report 2 high-level **component-shape lemmas + `Eq.trans`** rather than simplification of the concrete goal.

Do not use `debug.skipKernelTC` as a successful result.

### Outcome D — A1 and A2 differ materially

Verify file/module imports, definition exposure, compile-time cache reuse, elaborated expression sharing, options, and source snapshots. Inspect whether the expected lemma type is genuinely identical in both environments. Benchmark cold and warm builds separately; report one-time API compilation separately from each consumer run.

Do not label the difference a `no_expose` improvement if no exposure attribute was involved.

## 6. A distinct question: can the original statements remain unchanged?

This must not be silently folded into A1. The Report 3 canonical consumer replaced `leftDerivedUpperStarComp/Id` with `moduleObjectDerivedPullbackComp/Id`. That changes the statement, even though the original `exact h2` and `congr 1` scripts then succeed.

If the project requires the **original** statements:

1. Keep Report 2 Y4 as the already validated answer. Its abstract helper lemmas are:
   - `dncSectionSquareCoherenceComp`;
   - `dncLHS_components`;
   - `dncRHS_components`.
2. Keep the goal-side composition expansion **out of concrete rewriting**. Y1a showed that a concrete `simp` step alone can cause a kernel timeout.
3. If a new canonical API is useful internally, test whether its lemmas can be used inside the abstract component proof without converting an entire `Iso.trans`/`NatTrans.app` composite between representations.
4. Apply abstract side lemmas **directly to the original goal** by unification, then combine with ordinary `Eq.trans`. Do not first prove a new-vocabulary theorem and finish with a whole-expression `exact` against an upstream-vocabulary statement.
5. Compare declared types at the elaborated expression level (binder-name-insensitive equality/universe checks), not just statement text. Report 2 verified this equivalence for its repaired version.

If the project explicitly permits a **new canonical public API**, prepare a migration proposal separately: preserve old compatibility statements where needed, document which consumers change, and benchmark the complete affected dependency graph. Do not claim that a changed statement is a drop-in compatible fix.

## 7. Why removal of the wrapper is not the current priority

`v_nowrap` in Report 3 replaced uses with a macro expanding to the raw left-derived functor; all three statements then failed elaboration around dependent `congrArg` lambdas and `.leftDerivedFunctor` with insufficiently determined schemes. Report 1 X3 similarly reported a statement-elaboration regression under bare re-spelling.

This rules out **that direct replacement strategy**, not every possible end-to-end architecture without a wrapper. A more carefully typed, fully consistent raw-functor API could be tested later, but it is lower priority than A1 because:

- the simple deletion route has already failed;
- the regular `def` wrapper can help head-based argument comparison;
- the reports give a much cheaper discriminator for the claimed benefit of opacity.

If revisiting removal, explicitly type the dependent lambda binders, eliminate mixed-vocabulary imports, and compare against A1 and P0. Do not repeat an untyped macro substitution under a higher heartbeat limit.

## 8. How to use opacity controls without shipping them

`attribute [irreducible]` and `@[no_expose]` are **different mechanisms**. They both produced fast canonical-vocabulary controls in Report 3, but that does **not** prove their semantics or reduction behavior are identical.

- `[irreducible]` changes elaborator transparency behavior; the kernel may still unfold the ordinary definition.
- `@[no_expose]` inside a real `module` prevents ordinary importers from accessing an implementation body, making some mixed-vocabulary defeq conversions unavailable. It can turn a slow conversion into a type error.
- An equality theorem such as `moduleObjectDerivedPullback_eq` can expose a **propositional** relationship, but it does not restore downstream *definitional* equality. Generic `rw` on huge concrete expressions can still be costly.

Use these controls only to answer a specific question, such as “which check disappears when the body cannot be unfolded?” Do not allow `@[no_expose]` into the final defining module even if it is fast. Also do not add public `opaque` declarations or `[irreducible]` as a substitute.

If A1 fails and only an opacity control works, **report an unsolved transparent-API problem** with the smallest missing conversion and the best transparent fallback (currently Y4). Do not weaken the user's final-code constraint.

## 9. Performance methodology and stopping conditions

Measure the following separately:

| Metric | Why it matters |
|---|---|
| Clean elaboration time | Distinguishes Meta defeq/instance synthesis from kernel checking |
| Per-declaration kernel time | Finds cost transferred to compositors, coherence, or `_proof_n` |
| Whole-file wall and user CPU | Catches proof splitting and process overhead |
| Peak RSS | Detects reduction/defeq memory blow-up |
| API module compilation | Avoids understating the cost of moving declarations into imports |
| Consumer compilation with cached API | Measures incremental downstream experience |
| Clean build of affected dependency closure | Measures the true cost of a proposed shared API migration |
| Statement identity and `#print axioms` | Guards compatibility and soundness |

Historical context: Report 2's full repaired file ran around **50–54 s wall / 44–47 s user / ~2.07 GB**; Report 3's same-file `[irreducible]` variant around **26.5–29.6 s wall / 22.5–25.7 s user / ~1.99 GB**, and the `no_expose` consumer around **9.5–12.4 s wall**, plus **~23.5 s to compile the API module once**. These are **different variants and build scopes on a heavily loaded machine**; do not rank them by wall time alone.

Stop a branch if:

- an isolated variant reproduces a known deterministic kernel timeout with no new information;
- a new helper costs as much as the old target;
- a candidate only passes with kernel skipping, changed checker options, or a new opacity mechanism;
- a statement-changing result is being presented as Track P completion;
- changing visibility produces type errors and there is no specific transparency hypothesis left to test;
- repeated tests exceed practical resource budgets without narrowing the smallest expensive comparison.

Do not repeatedly increase heartbeats or create many parallel Lean builds.

## 10. Required deliverables for this round

Produce all of the following even if A1 fails:

1. **Variant table:** exact source diff, statement-vocabulary track (P/A), wrapper transparency, module layout, proof structure, compile result, failing phase, wall/user/system CPU, RSS, elaboration and kernel times.
2. **The A1 discriminator:** verified result of removing only `[irreducible]` from the Report 3 canonical API positive control. State clearly whether ordinary `def` alone works under that *exact* setup.
3. **Causal interpretation:** separate evidence for vocabulary alignment, ordinary regular-definition heads, elaborator reducibility, and module visibility. Mark untraced kernel reduction paths as hypotheses.
4. **A minimal checked source artifact:** if successful, provide a transparent candidate and all required helper/API definitions. If unsuccessful, retain the best partial variant without manufacturing a final fix.
5. **Compatibility assessment:** exact original-statement preservation or explicit API change, plus at least one real downstream importer if a shared API was modified.
6. **Soundness checks:** ordinary kernel, no new axioms or `sorry`, no final `HEq`, and **no final `opaque`, `@[no_expose]`, or new `[irreducible]` setting**.
7. **Performance comparison:** per-declaration and combined timings, imported module cost, and at least three comparable runs for the most promising candidate.
8. **Next-step decision:** recommend (a) keeping Report 2 Y4, (b) adopting a transparent canonical API in an explicitly approved scope, or (c) further targeted diagnosis. Do not declare an all-project solution without all-project evidence.

Suggested report skeleton:

```text
Environment
  Lean/Mathlib/git; effective options; machine load; source snapshots

Question
  Is canonical vocabulary sufficient without opacity?
  Is preserving the original theorem statement mandatory for this candidate?

Controls
  P0 (original-statement Y4), M0 (mixed failure),
  A3/A4 (diagnostic opacity positives)

A1 missing control
  exact one-line diff from v_irr
  compiled? elaboration? kernel? CPU/RSS?

Further experiments
  A2 imported transparent API; additional targeted variants if needed
  specific failure, expected binder, Expr differences, cost location

Compatibility
  original elaborated theorem types unchanged? yes/no
  downstream importer and dependency impacts

Validation
  no opaque/no_expose/new irreducible; no final HEq/sorry/axioms
  normal kernel; all helpers; module costs; repeated timings

Conclusion
  what is experimentally established?
  what remains uncertain?
  least-invasive next experiment and recommended final track
```

## 11. Execution priority

1. **First, run A1:** copy Report 3's `v_irr` successful canonical-vocabulary variant and remove *only* its `[irreducible]` attribute. No other edits.
2. **If A1 passes:** repeat, then run A2 (ordinary transparent imported API), validate every helper and the API-change boundary, and decide whether Track A is worth a separate downstream migration.
3. **If A1 fails:** locate the exact elaborator/kernel check that the attribute was suppressing, then trial a regular named interface, explicit dependent binder typing, or the existing abstract component boundary. Do not ship the attribute.
4. **For original statements:** keep Report 2 Y4 intact as the fallback; any new approach must beat or complement it **without silently changing theorem types**.
5. **Only after these controls:** decide whether larger wrapper removal, module-boundary redesign, or more intrusive tooling can answer an unresolved question.

**Go/no-go rule:** A convincing final repair must pass normal kernel checking, avoid all forbidden opacity mechanisms, account for total CPU/RSS and imported compilation, and explicitly state whether it preserves the original theorem API. The current investigation is complete when the missing A1 comparison and its consequences are measured—not when a preferred architecture is assumed to be correct.
