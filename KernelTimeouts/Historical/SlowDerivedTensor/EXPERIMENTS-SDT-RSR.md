# Slow Derived Tensor, round 12: reduction strategy and decision mechanism

## Evidence and boundary

This is Research B. `[R1]` denotes the fresh direct original-root READY4.2 replay in
`sdtide2/root-base.out` and `root-base.err`. `[R2]` denotes the fresh, observationally
instrumented original-root replay in `root-instrumented.out`, `root-instrumented.err`,
and `root-focused.jsonl`. `[R3]` denotes the pinned Lean implementation audit and
`sdtide2/instrumentation.patch`. `[R4]` denotes the fresh direct child replay in
`sdtide2/transparency.out`. `[R5]` denotes the Kernel-checked real-provider metadata
controls in `hints-base.out`, `hints-instrumented.out`, and `hints-focused.jsonl`.
`[A1]` and `[A2]` refer to the separate instance-decomposition report and its data.
The root is the Kernel comparison of the checked type of `icd_tensorObj_probe` with its
stored type after the same twelve-binder opening as round 11. The consumer and standard
library are pinned to Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11cda51a86af692955474`,
consumer `bdab171985a5e6c6e44fc3920386b89fc5627ca3`, and Lean source
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. [R1, R3]

No conversion rule, typeclass-search rule, or reduction choice was changed. The C++ patch
adds only event logging and transient counters for inference and proof-type comparison
depth. The Meta implementation is audited as the corresponding API path; this root calls
`Kernel.isDefEq`, so its actual decisions occur in `src/kernel/type_checker.cpp`, not in
`Lean/Meta/ExprDefEq.lean`. [R3]

## Original-root sequence and context

The final instrumented replay returns `true` in 71,285 ms and records 6,239,533
defeq calls, all successful, as in the fresh uninstrumented root replay. At call 67,
the pair of `CategoryTheory.Functor.proj` expressions is unchanged by initial cheap
WHNF; `projection_whnf` changes both heads to
`CategoryTheory.MonoidalCategoryStruct.tensorObj`. Call 68 is its
`whnf-iota-exposure` child. Its initial cheap WHNF also changes neither head.
The first lazy-delta decision sees two `tensorObj` delta candidates, both with
height 0 and rank 0, and selects both, checked first. Events 178 and 179 unfold
those projection definitions on the checked and stored sides. The next decision
sees `MonoidalCategoryStruct.proj` on both sides with no delta candidate. [R2]

Call 68 then enters the projection-reducing second `whnf_core` pair. The checked
request unfolds `MonoidalCategory.toMonoidalCategoryStruct` (event 180) and the
direct canonical `HomotopyCategory.MonoidalCategory.instMonoidalCategory` (181).
Only after that request returns does the stored request unfold
`toMonoidalCategoryStruct` (182),
`instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures` (183), and the
canonical declaration inside its body (184). The canonical and shortcut heights
are respectively 24 and 25, but they are never the two candidates in the
call-68 lazy-delta decision. [R2, R3]

At event 183 the context stack is call 68 `tensorObj` pair, parent call 67
`Functor.proj` pair, then a `CategoryTheory.Quotient.as` argument and the
`Functor.HasLeftDerivedFunctor₂` proposition-type comparison at call 11. The
active counters are `proof_type_depth=1`, `infer_depth=0`. Thus this is a nested
structure-field projection/value comparison *within* proof irrelevance's
comparison of proposition types. It is not a direct comparison of the two
monoidal provider values, and the proposition-type ancestor alone would not
identify the inner request. [R2]

## Implementation path

In the pinned Kernel `is_def_eq_core`, a quick comparison precedes an initial
`whnf_core(t, false, true)` / `whnf_core(s, false, true)` pair. That pass avoids ordinary
delta and full projection reduction. The function then tries proof irrelevance, lazy
delta, the projection-specific comparison for Expr projections, and a second
`whnf_core(t_n)` / `whnf_core(s_n)` pair. If the second pair changes either term,
it recurses on the reduced pair. `whnf_core` performs beta, zeta, recursor, and
projection steps; `whnf` wraps it in a loop that additionally calls
`unfold_definition` on an exposed head. [R3]

The pinned `lazy_delta_reduction_step` first asks `is_delta` about the *current pair*
of heads. A single candidate selects that side (subject to its projection-app
exception); two candidates are ranked by reducibility hints; equal hints can first
test same-head arguments, then unfold both in checked/stored order. The regular
height values of later nested providers matter only if those provider heads are
the two candidates at the same decision point. The Kernel has no Meta transparency
mode in this comparison; the relevant `is_delta` test requires a value-bearing
declaration with matching universe-parameter count. [R3]

In `Lean/Meta/ExprDefEq.lean`, `isDefEqDeltaStep` also compares delta-candidate
hints and chooses left, right, or both. `isDefEqProjDelta` uses that step for
projection arguments, and `whnfCoreAtDefEq` can request `.yesWithDeltaI`
projection reduction under the lazy-WHNF option. These are implementation
counterparts, not executed event labels for the Kernel root. The Meta source
does not by itself classify event 183 or determine its Kernel side order. [R3]

## Transparency and provider metadata controls

The fresh extracted-provider replay shows the following Meta behavior. Projection
heads for `tensorObj`, `whiskerLeft`, and `whiskerRight` remain unexpanded at
`.reducible` and `.instances`; all three expose canonical versus shortcut
subexpressions at `.default` and `.all`. This is a child replay, not the
original Kernel root. [R4]

| Meta transparency | Checked provider WHNF | Stored provider WHNF | Meta DefEq |
|---|---|---|---|
| `.reducible` | `toMonoidalCategoryStruct` | `toMonoidalCategoryStruct` | false |
| `.instances` | `DerivedCategory..._aux_1` | `MonoidalCategory` projection | false |
| `.default` | `MonoidalCategoryStruct.mk`, 58 canonical occurrences | same constructor, 58 shortcut occurrences | true |
| `.all` | `MonoidalCategoryStruct.mk`, 58 canonical occurrences | same constructor, 58 shortcut occurrences | true |

The real-provider control clones the canonical and shortcut *definitions*, preserving
their exact declaration types and bodies while setting regular reducibility heights
to 24 or 25. It reuses the extracted original application arguments and local
context. `checkWithKernel` and `Kernel.check` pass for every constructed
application. All four direct application comparisons return Kernel DefEq `true`;
their WHNFs have `MonoidalCategory.mk` heads and remain structurally different.
This is an API-level counterfactual, not a replay of the original projection context.
The cloned shortcut body still references the original canonical declaration, so
this control does not replace every transitive provider occurrence in the original
root. [R5]

| Control | Canonical / shortcut height | DefEq | First actual delta / representation |
|---|---:|---|---|
| original direct pair | 24 / 25 | true | stored shortcut first at root 4367, call 1; checked canonical not unfolded there |
| equal 24 | 24 / 24 | true | checked canonical, then stored shortcut at root 5204, call 1 |
| equal 25 | 25 / 25 | true | checked canonical, then stored shortcut at root 6041, call 1 |
| swapped | 25 / 24 | true | checked canonical, then stored shortcut at root 6878, call 1 |

All four WHNFs have `MonoidalCategory.mk` heads and remain structurally unequal.
The focused provider log records the indicated first actual delta, side, and
height; the equality and WHNF results are recorded independently in
`hints-instrumented.out`. The 24/25 direct pair chooses the higher-height stored
shortcut first; equal heights choose checked first, and swapping the heights
chooses the checked canonical first. This establishes a hint effect for the
direct extracted provider pair. None of these direct comparisons reproduces
the original root's projection context or its 181 -> 183 -> 184 sequence. [R5]

## Decision and relation to Research A

The original-root order is determined locally by two different mechanisms.
At call 68, lazy delta sees *equal projection heads* (`tensorObj`, height 0), so
it unfolds both in checked/stored order. The resulting `proj` pair has no delta
candidate. The second `whnf_core` request processes the checked expression
before the stored expression, and `reduce_proj` calls ordinary `whnf` on each
projection's major premise. That unary WHNF exposes first the direct canonical
body, then the stored shortcut and its nested canonical body. At no selection
point in this sequence are the height-24 canonical and height-25 shortcut heads
compared against each other. Their metadata affects direct provider comparisons,
as the controls demonstrate, but does not select event 181 before event 183 in
this original-root path. This is a conclusion about this local event order, not
a claim that hints are irrelevant to every later defeq step. [R2, R3, R5]

The projection request also explains why the representations survive until this
boundary. Initial cheap WHNF and the projection-sensitive path leave the major
premises unexpanded. Once the second WHNF permits full projection reduction,
`whnf` must expose each monoidal structure's constructor to project the field;
ordinary delta and beta expose the canonical and shortcut provider bodies.
The Meta `.reducible`/`.instances` outcomes are consistent with different
exposure boundaries, but are not the Kernel's mode or the cause of its order.
[R2, R3, R4]

Research A establishes that the direct canonical application and the one inside
the shortcut differ in ten arguments, including `_proof_2` inside canonical
argument 9 and `_proof_1` at argument 11. Every exposed monoidal data and law
field has a first structural difference through argument 9, while each field
pair is Kernel DefEq. Those are representation and origin results. This report's
event evidence establishes when the Kernel exposes the shortcut and canonical
body; it does not infer a reduction decision from the field differences. [A1, A2, R2]

## Reproducibility and acceptance

The reduced data live in `sdtide2/`. The root probes `ide-root.lean` and
`ide2-b-hints.lean` run in the copied pinned consumer checkout `sdt-ide2/hist`
with its existing package oleans; `ide-r5a.lean`, `ide2-a.lean`, and
`ide2-providers.lean` are independent child probes. Use the pinned READY4.2
binary/library for the A and transparency controls. The instrumented binary is
built from the pinned Lean source plus `instrumentation.patch`, in the isolated
`sdt-ide2` tree, with CMake `USE_LAKE=OFF` and `make -j2` under a 3600-second
timeout. The patch has only logging and depth counters. A replay sets
`LEAN_PATH` to the copied checkout's `lake env printenv LEAN_PATH` plus the
copied stage-1 library, sets `LD_LIBRARY_PATH` to the stage-1 library, and
sets `LEAN_DEFEQ_ANATOMY=trace`. The root also sets
`LEAN_DEFEQ_MPRWE_ROOT=557`, `LEAN_DEFEQ_MPRWE_MAX_EVENTS=200000`,
`LEAN_DEFEQ_MPRWE_EVENTS` to a scratch JSONL path, and
`LEAN_DEFEQ_IDE2_EVENTS` to a separate scratch JSONL path; the hint control
uses the last variable for its focused log. The raw 139 MB root trace remains
only in scratch; `root-focused.jsonl` is a reduced event extract. The build and
Lean replays were wrapped in `timeout 3600`. The Weil filesystem remained at
84% use. [R1-R5]

One operational exception must be recorded: an initial isolated build used the
default stage-1 Lake worker pool and briefly started more than the allowed
three Lean/Lake processes. That build was stopped; the copied stage-1 build was
reconfigured with `USE_LAKE=OFF` and completed using at most two compiler jobs
from this run. No shared checkout was edited. This exception means the run did
not fully meet the process-cap protocol, despite the completed scientific
measurements. [R3]

| Criterion | Outcome |
|---|---|
| Canonical applications compared argument by argument | Complete in `EXPERIMENTS-SDT-IDD.md`. [A1] |
| All parent/law first differences traced | Complete for all 18 fields; deeper unequal subtrees are not exhaustively inventoried. [A1] |
| Event 183 comparison context | Identified: call 68 nested `tensorObj` value comparison inside call 11 proposition-type comparison, `proof_type_depth=1`, `infer_depth=0`. [R2] |
| Event 181 -> 183 -> 184 decision mechanism | Equal-height `tensorObj` lazy delta, then second WHNF checked before stored; projection-major-premise WHNF exposes the providers. [R2, R3] |
| Real-provider hint contribution | Direct provider controls show a hint effect; original call 68 never ranks the 24/25 providers, so those hints do not choose this event order. The direct controls are not a one-factor original-root replay. [R2, R3, R5] |
| Independent artifacts and final original-root validation | Complete: separate A and B probes, source patch, focused traces, all control applications Kernel-checked, and final root result `true`. Process-cap protocol exception above. [A1, A2, R1-R5] |
