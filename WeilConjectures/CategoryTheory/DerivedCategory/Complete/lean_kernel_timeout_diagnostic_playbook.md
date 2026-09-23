# Lean Kernel Timeout and Definitional-Equality Performance: A Diagnostic Playbook

## 1. Scope

This document is a reusable workflow for diagnosing Lean declarations that:

- elaborate quickly but take a very long time in kernel checking;
- hit a kernel timeout even though the elaborator appears finished;
- behave well in an abstract setting but become extremely slow after instantiating a complicated category, structure, or typeclass graph;
- are accepted quickly with `debug.skipKernelTC`, but take seconds or minutes normally.

The main goal is to answer, in order:

1. Is the slowdown in elaboration or in kernel checking?
2. If it is in the kernel, is the kernel checking the proof term itself, or is it proving an inferred type definitionally equal to the declared type?
3. If definitional equality is slow, what is the smallest expensive pair of expressions?
4. Why does the kernel reduce that pair in an expensive way?
5. Is the appropriate remedy:
   - a better abstraction boundary,
   - `@[no_expose]`,
   - changing an `abbrev` into a regular `def`,
   - restructuring a declaration so both sides share the same syntax,
   - or, in rarer cases, a kernel heuristic change?

The workflow deliberately separates **measurement** from **remediation**. Do not begin by adding `@[no_expose]`, changing priorities, or rewriting instance graphs. First locate the expensive kernel operation.

---

# 2. The Kernel-Checking Model to Keep in Mind

For a declaration such as:

```lean
lemma foo : DeclaredType := value
```

the relevant kernel work can be thought of schematically as:

```text
check DeclaredType
      │
      ▼
Kernel.check(value)
      │
      └── produces InferredType
      │
      ▼
Kernel.isDefEq(InferredType, DeclaredType)
```

This distinction is fundamental.

A declaration may have:

```text
Kernel.check(value)                      1 ms
Kernel.isDefEq(InferredType, DeclaredType) 90 s
```

In that situation:

- the proof term is not large or difficult to check;
- proof construction is not the bottleneck;
- elaboration is not the bottleneck;
- the problem is a definitional-equality reduction path.

Conversely, if `Kernel.check(value)` itself is slow, the investigation should focus on the proof/value term rather than only on the final expected-vs-inferred type conversion.

---

# 3. Phase 0: Build a Stable Benchmark

Before diagnosing anything, make the slowdown reproducible.

Prefer a small file containing only:

- the imports actually needed;
- the declarations needed to instantiate the problem;
- one slow declaration.

Measure wall-clock time with the same command each time.

For example:

```bash
time lake env lean KernelPerf.lean
```

Do not rely only on editor highlighting or elaborator profiling. A kernel-only slowdown can be almost invisible to elaborator-oriented profiling.

Record at least:

```text
Lean version / commit:
mathlib commit:
machine:
baseline wall time:
```

When comparing custom Lean builds, use the exact same Lean revision as the project toolchain whenever possible so that existing `.olean` files remain compatible.

---

# 4. Phase 1: Prove That the Kernel Is the Bottleneck

## 4.1 `debug.skipKernelTC`

Make a copy of the slow declaration and wrap it with:

```lean
set_option debug.skipKernelTC true in
lemma foo_skip : Target :=
  proof
```

### Interpretation

| Result | Meaning |
|---|---|
| normal: 60 s, skip: 0.2 s | The slowdown is in kernel checking. |
| normal: 60 s, skip: 55 s | The slowdown is mostly elaboration/meta/typeclass work. |
| skip version is also slow | Do not instrument the kernel yet; first profile elaboration. |

This is the first major fork in the debugging process.

---

## 4.2 Do not confuse fast `#synth` with fast kernel checking

A very common mistake is:

```lean
#synth SomeHugeInstance T
```

finishes quickly, therefore the instance cannot be involved.

This conclusion is invalid.

`#synth` measures the elaborator/typeclass search finding an instance. Later, the kernel may still need to prove two independently elaborated instance expressions definitionally equal, and that comparison may be extremely expensive.

Therefore distinguish:

```text
"Can Lean find this instance quickly?"
```

from:

```text
"Can the kernel cheaply compare two occurrences of this instance expression?"
```

---

# 5. Phase 2: Separate the Two Sides of the Declaration

Suppose the original declaration is:

```lean
lemma foo : ExplicitTarget :=
  rhs
```

Run two control experiments.

## 5.1 Let the RHS determine the type

```lean
def foo_raw :=
  rhs
```

If `foo_raw` kernel-checks quickly, the RHS proof/application itself is probably not expensive.

## 5.2 Keep the target, replace the value with `sorry`

```lean
lemma foo_target_only : ExplicitTarget := by
  sorry
```

If this is also fast, then:

```text
RHS alone       fast
Target alone    fast
Combined        slow
```

is very strong evidence that the expensive step is the kernel conversion:

```text
type(rhs) =?= ExplicitTarget
```

### Interpretation

| `foo_raw` | `foo_target_only` | original | Likely diagnosis |
|---|---|---|---|
| fast | fast | slow | Final kernel `isDefEq` |
| slow | fast | slow | RHS/value checking |
| fast | slow | slow | Declared type itself is expensive |
| slow | slow | slow | Multiple problems; minimize further |

This simple three-way experiment often saves hours of speculative debugging.

---

# 6. Phase 3: Replay Kernel Checking Directly

Once the slowdown appears to be kernel-only, insert the declaration with `debug.skipKernelTC` and manually replay kernel checking.

The following probe is useful:

```lean
open Lean Elab Command

private def probeKernelDecl (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let lctx : LocalContext := default

  let some info := env.find? declName
    | throwError m!"cannot find declaration {declName}"

  let value := info.value! true
  let declaredType := info.type

  logInfo m!""
  logInfo m!"============================================================"
  logInfo m!"Kernel probe: {declName}"
  logInfo m!"============================================================"

  logInfo m!"value sizeWithoutSharing: {value.sizeWithoutSharing}"
  logInfo m!"declared type sizeWithoutSharing: {declaredType.sizeWithoutSharing}"

  let checkStart ← IO.monoMsNow

  let inferredType ←
    match Kernel.check env lctx value with
    | .ok ty => pure ty
    | .error _ =>
        throwError m!"Kernel.check failed for {declName}"

  let checkEnd ← IO.monoMsNow

  logInfo m!"Kernel.check(value): {checkEnd - checkStart} ms"
  logInfo m!"inferred type sizeWithoutSharing: {inferredType.sizeWithoutSharing}"
  logInfo m!"Expr.equal inferred declared: {Expr.equal inferredType declaredType}"

  let forwardStart ← IO.monoMsNow

  let forwardResult ←
    match Kernel.isDefEq env lctx inferredType declaredType with
    | .ok result => pure result
    | .error _ =>
        throwError m!"forward Kernel.isDefEq failed for {declName}"

  let forwardEnd ← IO.monoMsNow

  logInfo m!"Kernel.isDefEq inferred → declared:"
  logInfo m!"  result: {forwardResult}"
  logInfo m!"  time:   {forwardEnd - forwardStart} ms"

  let reverseStart ← IO.monoMsNow

  let reverseResult ←
    match Kernel.isDefEq env lctx declaredType inferredType with
    | .ok result => pure result
    | .error _ =>
        throwError m!"reverse Kernel.isDefEq failed for {declName}"

  let reverseEnd ← IO.monoMsNow

  logInfo m!"Kernel.isDefEq declared → inferred:"
  logInfo m!"  result: {reverseResult}"
  logInfo m!"  time:   {reverseEnd - reverseStart} ms"

  logInfo m!"============================================================"
```

Run it on a declaration inserted using:

```lean
set_option debug.skipKernelTC true in
lemma foo_kernelProbe : Target :=
  proof

set_option maxHeartbeats 0 in
run_cmd do
  probeKernelDecl ``foo_kernelProbe
```

The exact kernel debugging API can change between Lean versions, so adjust small syntactic details to the project's toolchain if necessary.

---

# 7. How to Interpret the Direct Kernel Probe

## Case A: `Kernel.check(value)` is slow

Example:

```text
Kernel.check(value): 45000 ms
Kernel.isDefEq:       10 ms
```

Focus on:

- large proof/value terms;
- deeply nested applications;
- proof fields whose types themselves need checking;
- generated structure values;
- projections that force large value terms.

Do not spend most of your effort on expected-vs-inferred type mismatch.

---

## Case B: `Kernel.check(value)` is fast, `Kernel.isDefEq` is slow

Example:

```text
Kernel.check(value):                      1 ms
Kernel.isDefEq(inferred, declared):   85000 ms
```

This is the classic definitional-equality pathology.

Move to:

1. kernel diagnostics;
2. expression minimization;
3. recursive slow-pair tracing.

---

## Case C: Forward slow, reverse fast

Example:

```text
inferred → declared: 50 s
declared → inferred: 20 ms
```

This strongly suggests an asymmetric reduction decision near the top of the comparison.

Investigate:

- `lazy_delta_reduction_step`;
- reducibility hints;
- which side is unfolded first.

---

## Case D: Both directions similarly slow

Example:

```text
inferred → declared: 85 s
declared → inferred: 90 s
```

This usually means both directions eventually enter the same expensive recursive subproblem.

Do not overfocus on the top-level orientation. Find the deepest slow pair.

---

## Expression sizes

`sizeWithoutSharing` is useful but should not be overinterpreted.

A 50,000-node type can check quickly, while a much smaller pair can take a minute if reduction repeatedly revisits expensive definitions.

Use size information to detect dramatic term blowups, not as a direct estimate of kernel runtime.

---

# 8. Phase 4: Use Kernel Diagnostics, but Interpret Them Carefully

For a normal declaration, try:

```lean
set_option diagnostics true in
set_option diagnostics.threshold 0 in
lemma foo : Target :=
  proof
```

Useful sections can include:

```text
[reduction] unfolded declarations
[reduction] unfolded reducible declarations
[def_eq] heuristic for solving `f a =?= f b`
[reduction] Axioms ... tried to be unfolded
[kernel] unfolded declarations
```

For huge outputs, raise the threshold:

```lean
set_option diagnostics.threshold 100
```

or:

```lean
set_option diagnostics.threshold 1000
```

---

# 9. How to Read Unfold Counters

Suppose diagnostics reports:

```text
Preadditive.homGroup       700000
Functor.obj                650000
NatTrans.app               540000
CategoryStruct.comp        200000
```

Do **not** immediately conclude:

> "`Preadditive.homGroup` is the bug."

A high counter often means:

> the kernel entered a bad reduction path somewhere much earlier, and this low-level declaration is simply where the path exploded.

Think in terms of:

```text
root cause
   ↓
bad high-level reduction decision
   ↓
implementation details exposed
   ↓
low-level structure projections
   ↓
hundreds of thousands of repeated reductions
```

The highest-frequency declaration may be the final victim rather than the first bad boundary.

---

# 10. A Better Question Than “What Is Unfolded Most?”

Once global counters are available, the next question should be:

> **Which pair of expressions is the kernel trying to prove definitionally equal when the expensive descent begins?**

This is much more informative than a histogram of unfolded constants.

The normal diagnostics do not answer this directly.

For serious kernel timeouts, instrument recursive `isDefEq`.

---

# 11. Phase 5: Find the Deepest Slow Recursive DefEq Pair

In a custom Lean build matching the project's exact Lean revision, instrument:

```cpp
type_checker::is_def_eq_core(expr const & t, expr const & s)
```

The precise function names and source layout are version-dependent, but the idea is stable.

For every recursive call:

1. record recursion depth;
2. record start time;
3. on return, if elapsed time exceeds a threshold, print:
   - depth;
   - elapsed time;
   - LHS head;
   - RHS head;
   - application arity;
4. for a small number of very slow calls, dump raw expressions.

Conceptual output:

```text
[DEFEQ-SLOW] depth=41 ms=8000 lhs=Quotient.lift rhs=Quotient.lift
[DEFEQ-SLOW] depth=32 ms=19000 lhs=NatTrans.app rhs=NatTrans.app
[DEFEQ-SLOW] depth=21 ms=24000 lhs=Functor.map rhs=Functor.map
[DEFEQ-SLOW] depth=13 ms=85000 lhs=SomeHighLevelHead rhs=SomeHighLevelHead
```

### How to interpret this trace

The shallowest slow call is often not the interesting one: it may simply wait for a deeper recursive comparison.

Prefer:

> the deepest call that is still very slow and whose children are no longer comparably expensive.

That pair is often the first useful “minimal expensive pair”.

---

# 12. Parallel-Descent Bisection

A useful refinement is to recursively compare corresponding subexpressions and search for:

> a differing pair that is expensive, but has no smaller expensive differing child pair.

This can identify cases such as:

```text
MonoidalCategoryStruct.tensorObj(...)
  =?=
MonoidalCategoryStruct.tensorObj(...)
```

where only one hidden argument is expensive.

Then compare arguments independently:

```text
arg 0: 0 ms
arg 1: 3 ms
arg 2: 135000 ms
arg 3: syntactically equal
arg 4: syntactically equal
```

This is much more actionable than a whole-declaration timeout.

---

# 13. Phase 6: Instrument `is_def_eq_args`

For a same-head application:

```text
f a₀ a₁ a₂
=?=
f b₀ b₁ b₂
```

instrument argument comparison and time each pair.

The ideal diagnostic is:

```text
head = f

arg 0: eq, 0 ms
arg 1: eq, 0 ms
arg 2: eq, 33 ms
```

If full unfolding takes 80 seconds while argument congruence takes 33 ms, the problem is not that the terms are intrinsically hard to compare. The problem is the kernel control flow choosing not to use cheap congruence before unfolding.

This distinction is crucial.

---

# 14. Reducibility: `abbrev` vs `@[reducible] def`

This was one of the most important lessons from the motivating case.

Consider:

```lean
abbrev Foo := ...
```

versus:

```lean
@[reducible]
def Foo := ...
```

They may behave similarly from the elaborator user's point of view, but they are not the same to the kernel.

Conceptually:

```text
abbrev
  elaborator: very transparent
  kernel reducibility hint: abbreviation

@[reducible] def
  elaborator: also easy to unfold
  kernel reducibility hint: regular(height)
```

The `@[reducible]` attribute mainly controls elaborator/meta transparency. The change from `abbrev` to `def` is what changes the kernel declaration's reducibility hint.

This matters because the kernel's lazy delta-reduction heuristics can treat regular definitions differently from abbreviations.

---

# 15. The Same-Head Congruence Trap

A particularly important kernel performance pattern is:

```text
f a₀ ... aₙ
=?=
f b₀ ... bₙ
```

where:

- both sides have the same head `f`;
- comparing the arguments is cheap;
- but `f` is an abbreviation-like declaration;
- the kernel unfolds `f` instead of first proving the arguments definitionally equal.

Unfolding may expose:

```text
structure fields
→ functor implementation
→ quotient/localization machinery
→ low-level algebraic structures
```

and turn a millisecond comparison into a minute-long one.

A diagnostic kernel patch can test this hypothesis:

> temporarily allow the same-head argument-comparison shortcut even when the declaration is not `regular`.

If runtime collapses dramatically, the mechanism has been confirmed.

This is a diagnostic experiment, not automatically a suitable global kernel fix.

---

# 16. Pure-Lean Control: Use a Regular Wrapper

Without modifying the kernel, a useful experiment is:

```lean
@[reducible]
def regularWrapper (args...) :=
  originalAbbrevHead args...
```

Then compare:

```text
originalAbbrevHead ...
=?=
originalAbbrevHead ...
```

against:

```text
regularWrapper ...
=?=
regularWrapper ...
```

### Interpretation

| Result | Meaning |
|---|---|
| wrapper becomes very fast | Kernel reducibility hint / same-head congruence is likely central. |
| wrapper remains slow | The problem resumes inside another abbreviation or deeper expression. |
| wrapper improves somewhat | Multiple abbreviation boundaries may be involved. |

Important: changing only the outer head may not help if the same problem immediately recurs at an inner abbreviation.

---

# 17. `abbrev → @[reducible] def` as a Local Remedy

When a slow chain is caused by a new high-level API alias, a practical library-side experiment is:

```diff
-abbrev HasSomething := ...
+@[reducible]
+def HasSomething := ...
```

This can preserve convenient elaborator behavior while giving the kernel a regular definition and enabling different definitional-equality heuristics.

Use this selectively.

Good candidates:

- high-level API aliases;
- propositions or structures that repeatedly appear as the same head on both sides;
- declarations directly identified by recursive defeq tracing;
- new abstractions introduced by the local branch/PR.

Poor candidates:

- random low-level definitions with huge unfold counters;
- declarations never observed in the slow recursive pair;
- fundamental global API definitions unless there is strong evidence.

After each change, rerun the slow-pair trace. The expensive pair may simply move to the next abbreviation in the chain.

---

# 18. `@[no_expose]`: What It Solves and What It Does Not

`@[no_expose]` is a different mechanism.

It is useful when:

> downstream kernel conversion should not be allowed to inspect a declaration's implementation body at all.

It can create an abstraction boundary between:

```text
public high-level term
        │
        X  no unfolding across this boundary
        │
implementation detail
```

But do not confuse this with `abbrev → def`.

### `@[no_expose]`

Controls whether the implementation body is exposed across module boundaries.

### `abbrev` vs `def`

Changes the kernel reducibility hint and therefore reduction strategy when the body *is* available.

These solve different problems.

---

# 19. How to Test a `@[no_expose]` Hypothesis

If the slow trace shows:

```text
HighLevelTerm
→ ImplementationA
→ ImplementationB
→ quotient/localization
→ enormous reduction
```

try putting the barrier at the highest implementation term that users should not definitionally depend on.

Possible outcomes:

### A. Runtime collapses and the declaration still succeeds

Excellent evidence that the body was unnecessarily exposed.

### B. Definitional equality now fails immediately

The body is semantically required for the current API's definitional equality. The barrier is too high, or the API relies too strongly on implementation-level defeq.

### C. No performance change

The expensive route does not pass through that body, or the bad decision occurs before this declaration.

Do not keep adding `@[no_expose]` deeper at random.

---

# 20. Why Changing Typeclass Priority Often Does Nothing

Suppose a declaration was elaborated earlier with hidden instance arguments:

```text
SomeStructure ... instance₁ ...
```

and the current target elaborates to:

```text
SomeStructure ... instance₂ ...
```

Changing instance priority now may affect newly synthesized terms, but it does not rewrite hidden arguments already baked into an imported theorem's type.

Therefore:

```text
"raise this instance priority"
```

is primarily an elaboration experiment.

If the slowdown is a kernel comparison between two already-constructed terms, priority changes may have little or no effect.

Use priority tuning only when there is evidence that synthesis itself is selecting an undesirable expression.

---

# 21. Sharing Instances: Useful Diagnostic, Not a Universal Fix

Explicitly sharing a local instance can test whether two independently synthesized data-valued instances are causing a mismatch.

For example:

```lean
letI shared : SomeStructure T := ...
```

or a binder:

```lean
[shared : SomeStructure T]
```

can sometimes collapse a slow comparison.

### Interpretation

| Result | Meaning |
|---|---|
| huge speedup | independently generated instance expressions were important |
| no change | stop focusing on instance identity and investigate reduction control flow |

Do not assume that all kernel defeq problems are instance-coherence problems.

---

# 22. Proof Irrelevance Can Still Be Expensive

A proof field being propositionally irrelevant does **not** imply that comparing two proof fields is free.

To use proof irrelevance, the kernel may need to establish:

```text
type(proof₁) =?= type(proof₂)
```

If those proposition types themselves contain difficult abbreviations or structure expressions, almost all runtime can occur before proof irrelevance discharges the actual proof terms.

A useful trace may show:

```text
[PROOF-IRREL] 70 s
proof lhs = sameConstant ...
proof rhs = sameConstant ...
type lhs  = SomeProp ...
type rhs  = SomeProp ...
```

The correct conclusion is:

> the proof body is irrelevant; the expensive object is the definitional equality of the proposition types.

This is especially important for:

- structure proof fields;
- functor laws;
- category laws;
- derived-functor existence/is-derived propositions.

---

# 23. Phase 7: Instrument Proof Irrelevance When Needed

If a recursive trace enters a generated proof such as:

```text
Functor.something._proof_3
```

do not immediately inspect the proof body.

Instrument the proof-irrelevance branch and record:

```text
proof heads
type(proof lhs)
type(proof rhs)
time spent comparing the proof types
```

If the proof-type comparison dominates runtime, continue debugging those types exactly as you would any other slow `isDefEq` pair.

---

# 24. Phase 8: Instrument Lazy Delta-Reduction Decisions

Once a minimal slow pair has been identified, instrument the kernel's lazy delta-reduction step.

For each relevant step, record:

```text
lhs head
rhs head
lhs reducibility hint
rhs reducibility hint
regular height, if applicable
chosen action
```

Possible actions include:

```text
compare arguments
unfold lhs
unfold rhs
unfold both
projection reduction
WHNF reduction
```

The important question is:

> **Why did the kernel decide to unfold here instead of using a cheaper comparison?**

This is the point where an abstract suspicion such as:

> "the kernel seems to be unfolding in the wrong direction"

can be converted into an exact control-flow observation.

---

# 25. Do Not Print Every Kernel Event

A minute-long defeq can contain enormous numbers of recursive calls.

Unfiltered tracing can:

- create gigabytes of logs;
- distort the performance problem;
- make the trace unusable.

Prefer:

1. time-thresholded slow-call logging;
2. recursion-depth filtering;
3. head-name filtering;
4. only a handful of full raw-expression dumps;
5. aggregation by `(lhs head, rhs head)` pair.

A pair-frequency table can be more useful than a single-declaration unfold counter:

```text
(lhsHead, rhsHead) → count
```

because it tells you which two implementations are repeatedly trying to converge.

---

# 26. Reproducer Minimization Strategy

When a large theorem times out, repeatedly strip layers while preserving the kernel pathology.

For example:

```text
large theorem
↓
property of a functor
↓
equality of functors
↓
equality of `obj`
↓
equality of one structure field
↓
one hidden instance argument
↓
one recursive kernel pair
```

The best reproducer is not necessarily the shortest Lean source.

The best reproducer is:

> the smallest expression that still triggers the same expensive kernel control-flow path.

---

# 27. Compare Abstract and Concrete Instantiations

A powerful control experiment is:

```text
abstract category C     fast
specific complicated C  slow
```

This means:

- the abstract construction itself is not sufficient to cause the problem;
- some concrete implementation becomes visible only after instantiation;
- the specific category may amplify an otherwise modest bad reduction choice.

Do not conclude that the concrete category's most frequently unfolded definition is the root cause.

It may simply make the wrong high-level reduction choice catastrophically expensive.

---

# 28. Common False Leads

## 28.1 “The most unfolded declaration is the bug”

Usually too simplistic.

High unfold count often identifies where the kernel ended up, not why it went there.

---

## 28.2 “`#synth` is fast, so instances are irrelevant”

False.

Kernel comparison of instance expressions is a separate problem.

---

## 28.3 “This structure is a `Prop`, so it cannot matter”

Its proof body may not matter, but its **type** can still participate in expensive definitional equality, especially through proof irrelevance.

---

## 28.4 “The theorem's pretty-printed types are identical”

Pretty printing hides:

- implicit arguments;
- instance arguments;
- universe instantiations;
- generated wrappers.

Use `pp.explicit`, `pp.instances`, `pp.fullNames`, or raw `Expr` inspection when necessary.

---

## 28.5 “Make everything opaque”

This can turn:

```text
slow but successful defeq
```

into:

```text
fast failure
```

Opacity is only correct when the API should not rely on the hidden body for definitional equality.

---

## 28.6 “Change all abbreviations to defs”

Too broad.

First identify which abbreviation heads are on the actual slow path. Regularizing a high-level head can be very effective, but mass conversion can change elaboration behavior and create unrelated regressions.

---

# 29. A Generic Decision Tree

Use the following sequence.

```text
Slow declaration
      │
      ▼
debug.skipKernelTC
      │
      ├── still slow ──► elaborator/meta/typeclass profiling
      │
      └── fast
           │
           ▼
      RHS-only vs Target-only
           │
           ├── RHS slow ──► proof/value investigation
           ├── target slow ─► type construction investigation
           └── both fast, combined slow
                    │
                    ▼
             Kernel.check vs Kernel.isDefEq
                    │
                    ├── Kernel.check slow
                    │       └── inspect value/proof term
                    │
                    └── Kernel.isDefEq slow
                            │
                            ▼
                    kernel diagnostics
                            │
                            ▼
                    recursive slow-pair trace
                            │
                            ▼
                    minimal expensive pair
                            │
                ┌───────────┼──────────────┐
                ▼           ▼              ▼
          same-head     proof irrelevance   different heads
          applications      path              / delta path
                │           │                  │
                ▼           ▼                  ▼
        time arguments   compare proof     trace lazy delta
                │          types              decisions
                ▼
       abbrev/regular?
                │
       ┌────────┴────────┐
       ▼                 ▼
 regularize API     test kernel heuristic
 alias locally      in custom build
```

---

# 30. Result Interpretation Matrix

| Observation | Strong implication | Next action |
|---|---|---|
| `skipKernelTC` removes delay | Kernel issue | Direct kernel probe |
| `foo_raw` fast, `foo_sorry` fast, original slow | Expected/inferred type conversion | `Kernel.isDefEq` |
| `Kernel.check` fast, `Kernel.isDefEq` slow | Pure defeq pathology | Slow-pair trace |
| forward slow, reverse fast | Top-level asymmetric heuristic | Delta-decision trace |
| both directions slow | Shared deep subproblem | Find deepest slow pair |
| global counters dominated by low-level algebra | Likely downstream explosion | Trace higher-level pair |
| same-head argument comparison cheap, normal defeq slow | Kernel unfolds instead of congruence | Check reducibility hint |
| custom no-guard kernel becomes fast | Abbrev/same-head heuristic confirmed | Local regular-def workaround or core issue |
| `@[reducible] def` fixes slowdown | Kernel regular hint is beneficial | Consider local API change |
| `@[no_expose]` fixes slowdown | Body should not be visible downstream | Keep as abstraction boundary candidate |
| `@[no_expose]` causes immediate failure | Defeq relies on body | Barrier too high / API too definitional |
| local instance sharing fixes slowdown | Instance-expression mismatch | Canonicalize/share construction |
| local instance sharing does nothing | Not mainly instance identity | Return to reduction tracing |
| proof-irrelevance trace is slow | Proposition-type defeq is slow | Trace proof types, not proof bodies |

---

# 31. A Reusable Kernel-Timeout Report Template

When handing a problem to another developer or agent, collect:

## Environment

```text
Lean version:
Lean commit:
mathlib commit:
OS / CPU:
```

## Baseline

```text
whole declaration wall time:
skipKernelTC wall time:
```

## Isolation

```text
RHS-only:
Target-only:
```

## Kernel probe

```text
value size:
declared type size:
inferred type size:

Kernel.check(value):
Kernel.isDefEq inferred → declared:
Kernel.isDefEq declared → inferred:
```

## Diagnostics

```text
top 20 [kernel] unfolded declarations:
top relevant [def_eq] entries:
opaque/non-exposed declarations the kernel tried to unfold:
```

## Recursive trace

```text
deepest slow pair:
depth:
elapsed:
lhs head:
rhs head:
lhs size:
rhs size:
```

## Argument breakdown

```text
arg 0:
arg 1:
...
```

## Reducibility

```text
lhs hint:
rhs hint:
same head?:
regular?:
abbrev?:
```

## Experimental interventions

```text
no_expose candidate:
abbrev → @[reducible] def:
shared local instance:
custom kernel heuristic:
```

## Interpretation

State explicitly:

```text
What is confirmed:
What is ruled out:
What remains a hypothesis:
```

This last distinction prevents future debugging from repeatedly revisiting already-disproved theories.

---

# 32. Worked Example: What the Derived-Tensor Case Taught

The motivating derived-tensor problem followed this progression:

1. The declaration elaborated quickly but kernel checking took one to two minutes.
2. `debug.skipKernelTC` made it nearly instantaneous.
3. The RHS theorem alone was fast.
4. The explicit target with `sorry` was fast.
5. `Kernel.check(value)` took about 1–3 ms.
6. `Kernel.isDefEq` took tens of seconds to minutes.
7. Global diagnostics showed hundreds of thousands of low-level additive/Hom unfoldings.
8. Those counters initially suggested several false leads:
   - typeclass priorities;
   - `Preadditive`;
   - `MonoidalPreadditive`;
   - sharing `HasDerivedCategory`;
   - `@[no_expose]` on deep derived terms.
9. Recursive `isDefEq` instrumentation found a much more informative chain:
   - a high-level same-head application;
   - descent through derived-functor fields;
   - generated proof types;
   - category composition;
   - equivalences;
   - natural transformations;
   - quotient/localization machinery.
10. Per-argument timing showed that direct argument congruence was cheap.
11. A diagnostic kernel build that allowed the same-head shortcut beyond `regular` definitions reduced runtime from roughly a minute to a few seconds.
12. This exposed a general abbreviation/reducibility issue rather than a single expensive mathematical construction.
13. Converting selected derived-functor `abbrev`s into `@[reducible] def`s successfully removed one major timeout path.
14. A separate lower-level `tensorObj` path remained, showing that different slow declarations can share a mechanism while still having different first problematic abbreviation boundaries.

The main methodological lesson is:

> The decisive step was not finding which declaration unfolded most often. It was finding the smallest expensive kernel comparison and then understanding why the kernel chose unfolding instead of cheap congruence.

---

# 33. Recommended Order for Future Kernel Timeouts

For a new, more complicated timeout, use this order:

1. **Baseline and `debug.skipKernelTC`.**
2. **RHS-only and target-only controls.**
3. **Direct `Kernel.check` / `Kernel.isDefEq` timing.**
4. **Kernel diagnostics with a moderate threshold.**
5. **Minimize the declaration while preserving the same kernel pathology.**
6. **Instrument recursive `isDefEq` and find the deepest slow pair.**
7. **Time corresponding arguments independently.**
8. **Inspect kernel reducibility hints of the slow heads.**
9. **If same-head abbreviation unfolding is suspected:**
   - test a regular wrapper;
   - test `abbrev → @[reducible] def`;
   - optionally test a custom kernel heuristic.
10. **If the trace enters proof fields:**
    - instrument proof irrelevance;
    - inspect proof *types*.
11. **If a body should never have been exposed:**
    - test `@[no_expose]`.
12. **Only after evidence points there:**
    - tune instance sharing or priority.
13. **After every successful change:**
    - rerun the slow-pair trace;
    - verify that the expensive pair disappeared rather than merely moved deeper.

---

# 34. Final Principles

1. **Separate elaboration from kernel checking first.**
2. **Separate proof checking from definitional equality second.**
3. **Global unfold counts are clues, not diagnoses.**
4. **The smallest expensive pair is more valuable than the largest counter.**
5. **Same-head congruence can be dramatically cheaper than unfolding.**
6. **`abbrev` and `@[reducible] def` can look similar to the elaborator but behave differently in the kernel.**
7. **`@[no_expose]` and reducibility hints solve different problems.**
8. **Proof irrelevance can still spend most of its time comparing proof types.**
9. **Typeclass priority changes only matter when synthesis itself is part of the problem.**
10. **Abstract-vs-concrete controls are extremely informative.**
11. **Instrument the kernel only after creating a small reproducer.**
12. **Make one controlled change at a time and record wall-clock results.**
13. **A good fix prevents the kernel from entering the bad path; it does not merely optimize the bottom of that path.**

The ultimate debugging question is:

> **What is the highest-level definitional equality that should have been resolved by cheap congruence or stopped at an abstraction boundary, but instead caused the kernel to descend into an expensive implementation?**
