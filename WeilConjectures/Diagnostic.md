# Lean Kernel Timeouts: Diagnostic and Remediation Guide

## 1. Goal

This guide is for Lean declarations that elaborate successfully but become extremely slow, time out, or are OOM-killed during kernel checking.

The central rule is:

> First identify which kernel phase is slow. Then identify the smallest expensive comparison. Only then choose a remedy.

Two distinct failure modes are especially important:

1. **Reduction-strategy failure**: the kernel unfolds a transparent/abbreviation-headed term instead of resolving a same-head application by cheap congruence.
2. **Proof-abstraction/type-boundary failure**: `abstractNestedProofs` rewrites proofs inside the value-side type, so the inferred type and declared type differ at many proof positions; proof irrelevance then recursively compares large proposition types carrying data-valued instances.

These two mechanisms need different fixes.

---

## 2. Kernel checking model

For:

```lean
def foo : DeclaredType := value
```

think of kernel work as:

```text
Kernel.check(DeclaredType)
Kernel.check(value)  ---> InferredType
Kernel.isDefEq(InferredType, DeclaredType)
```

Do not assume which step is expensive.

---

## 3. First triage: kernel or elaborator?

Use:

```lean
set_option debug.skipKernelTC true in
def foo : T := value
```

Interpretation:

| Result | Meaning |
|---|---|
| normal: minutes, skip: seconds | kernel problem |
| both slow | elaborator / typeclass / meta problem |
| skip moderately faster | mixed problem |

A fast `#synth` does **not** prove kernel conversion is cheap. Typeclass synthesis and kernel comparison of instance expressions are separate issues.

---

## 4. Three cheap discriminators before instrumentation

### 4.1 Type-only control

Restate the slow type as an axiom:

```lean
axiom foo_type_only (x : X) : HugeType x
```

- Fast: the type itself is cheap.
- Slow: the type is intrinsically hard for the kernel.

### 4.2 Put the suspicious expression in value position

```lean
def probe (x : X) : Type _ := HugeType x
```

- Fast: the expression itself is cheap to kernel-check.
- Slow: inspect its internal applications/subterms.

### 4.3 Replace a concrete heavy instance by a hypothesis

```lean
def probe [h : HugeStructure D] : ...
```

instead of exposing a synthesized instance in the type.

- Large speedup: the concrete instance expression is an amplifier.
- No change: look elsewhere.

This test is particularly useful for `MonoidalCategory`, `HasDerivedCategory`, sheafification/localization structures, and similar proof-carrying data.

---

## 5. Replay kernel phases directly

Insert a declaration with `debug.skipKernelTC`, then inspect its stored value and type.

```lean
open Lean Elab Command

private def probeKernelDecl (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let lctx : LocalContext := default

  let some info := env.find? declName
    | throwError m!"cannot find {declName}"

  let value := info.value! true
  let declaredType := info.type

  let t0 ← IO.monoMsNow
  let inferredType ←
    match Kernel.check env lctx value with
    | .ok ty => pure ty
    | .error _ => throwError "Kernel.check(value) failed"
  let t1 ← IO.monoMsNow

  logInfo m!"Kernel.check(value): {t1 - t0} ms"
  logInfo m!"Expr.equal inferred declared: {Expr.equal inferredType declaredType}"

  let t2 ← IO.monoMsNow
  let r ←
    match Kernel.isDefEq env lctx inferredType declaredType with
    | .ok r => pure r
    | .error _ => throwError "Kernel.isDefEq failed"
  let t3 ← IO.monoMsNow

  logInfo m!"Kernel.isDefEq: {r}, {t3 - t2} ms"
```

For steps that may never return, log to an `IO.FS.Handle` and flush. `IO.println` inside `run_cmd` may be captured until the command finishes.

---

## 6. How to interpret the split

### Case A — `Kernel.check(value)` slow

Investigate:

- application argument conversions;
- structure-valued terms;
- projections;
- local expected-vs-inferred domain conversions.

Use prefix/subterm timing.

### Case B — `Kernel.check(value)` fast, `Kernel.isDefEq` slow

Immediately ask:

```text
Are InferredType and DeclaredType structurally identical?
```

If not, structurally diff them **before** adding C++ kernel instrumentation.

### Case C — both directions of `isDefEq` similarly slow

The problem is probably a shared deep recursive subproblem, not just a top-level left/right unfolding choice.

---

## 7. Structural diff is a first-class diagnostic

If:

```lean
Expr.equal inferredType declaredType
```

is false, recursively find minimal differing subterms.

```lean
partial def diffs
    (path : String) (a b : Expr) :
    Array (String × Expr × Expr) :=
  if a.equal b then #[]
  else match a, b with
  | .app .., .app .. =>
      let fa := a.getAppFn; let fb := b.getAppFn
      let aa := a.getAppArgs; let ab := b.getAppArgs
      if fa.equal fb && aa.size == ab.size then Id.run do
        let mut out := #[]
        for h : i in [0:aa.size] do
          out := out ++ diffs s!"{path}.{i}" aa[i]! ab[i]!
        return out
      else #[(path, a, b)]
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ =>
      diffs (path ++ ".dom") d₁ d₂ ++ diffs (path ++ ".bod") b₁ b₂
  | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ =>
      diffs (path ++ ".dom") d₁ d₂ ++ diffs (path ++ ".bod") b₁ b₂
  | .mdata _ x, y => diffs path x y
  | x, .mdata _ y => diffs path x y
  | .proj _ _ x, .proj _ _ y => diffs (path ++ ".p") x y
  | _, _ => #[(path, a, b)]
```

Interpretation:

- no differences: look elsewhere;
- a few data differences: isolate those;
- many proof-only differences: investigate `abstractNestedProofs`;
- same head but different hidden arguments: time arguments independently and inspect reducibility.

---

## 8. Failure mode I: bad same-head reduction strategy

Typical shape:

```text
f a₀ ... aₙ =?= f b₀ ... bₙ
```

where argument comparison is cheap, but the kernel unfolds `f` and exposes an enormous implementation.

This often happens around abbreviation-like heads.

### Diagnostic tests

1. Time each argument pair using kernel `isDefEq`.
2. Try a regular wrapper:
   ```lean
   @[reducible]
   def fRegular args := f args
   ```
3. In a custom kernel, test whether allowing same-head argument comparison beyond `regular` heads collapses runtime.

If full conversion takes 80 seconds but argument congruence takes 30 ms, the problem is control flow, not intrinsic complexity.

---

## 9. `abbrev` versus `@[reducible] def`

These can feel similar to the elaborator but differ in the kernel.

```text
abbrev
  elaborator: very transparent
  kernel hint: abbreviation

@[reducible] def
  elaborator: easy to unfold
  kernel hint: regular(height)
```

The kernel may use different lazy-delta heuristics for them.

### Constructive remedy

If a high-level API alias is on the actual slow path:

```diff
-abbrev Foo := ...
+@[reducible]
+def Foo := ...
```

can preserve elaborator convenience while giving the kernel a regular head.

Do this selectively, not globally.

---

## 10. Failure mode II: `abstractNestedProofs` changes the inferred type

A more subtle timeout occurs when the declaration type itself is cheap, and the value itself is cheap, yet final `isDefEq` is catastrophic.

Lean abstracts nested proofs in definition values into auxiliary theorems such as:

```text
Foo._proof_1
Foo._proof_2
```

When proofs occur inside type expressions nested in the value, those proof occurrences can be rewritten too.

The declared type is not necessarily rewritten in the same way.

Result:

```text
DeclaredType:
  BigType (... rawProof₁ ...) (... rawProof₂ ...)

InferredType:
  BigType (... Foo._proof_1 ...) (... Foo._proof_2 ...)
```

If a structural diff finds many minimal differences and all are proofs, this mechanism should be investigated immediately.

---

## 11. Why proof irrelevance can still be catastrophically expensive

To compare proof values:

```text
p₁ =?= p₂
```

the kernel may first need:

```text
type(p₁) =?= type(p₂)
```

If those proposition types carry data-valued instances such as:

```text
MonoidalCategory C
HasDerivedCategory C
IsGrothendieckAbelian C
```

then proof irrelevance recursively re-enters large instance expressions.

A proof-only mismatch can therefore fan out through:

```text
proof
→ proposition type
→ data-valued instance
→ more proof fields
→ more proposition-type comparisons
```

Symptoms include:

- multi-minute deterministic timeout;
- OOM / exit 137;
- many structurally different proof positions;
- tiny syntax but huge conversion time.

---

## 12. Best fix for proof-laden declared types: name the heavy object

Suppose a data definition is stated over:

```lean
Cone (bigFunctor ⋙ tensorLeft K)
```

and `tensorLeft K` expands to a sophisticated monoidal instance containing many proofs.

Instead introduce:

```lean
noncomputable def completionDiagram (K : D) :
    ℕᵒᵖ ⥤ D :=
  bigFunctor ⋙ tensorLeft K
```

and state downstream data as:

```lean
noncomputable def completionCone (K : D) :
    Cone (completionDiagram K) :=
  ...
```

This moves the heavy proof-carrying expression into the **body** of a named definition.

Downstream declared types contain only:

```text
completionDiagram K
```

rather than the full implementation tree.

This is often much more robust than transparency tuning.

---

## 13. Why the abstraction boundary works

The change is architectural:

```text
Before:
declared type contains
  HugeConstruction (large proof-carrying instance tree)

After:
declared type contains
  NamedThing smallArgs
```

The heavy construction is checked once in the named definition body.

The kernel no longer repeatedly reconciles independently elaborated proof trees inside downstream types.

---

## 14. Do not puncture a successful boundary

A convenience lemma like:

```lean
lemma completionDiagram_def :
    completionDiagram K = bigFunctor ⋙ tensorLeft K := rfl
```

may reproduce the timeout.

Why?

- the stored body of `completionDiagram` may already contain abstracted `_proof_k` constants;
- the fresh RHS contains raw proofs;
- `rfl` asks the kernel to reconcile exactly the proof-position mismatch the boundary was designed to avoid.

Therefore:

> A good performance boundary should usually remain part of the public API.

Prefer downstream statements in terms of the named object.

---

## 15. Data definitions are more dangerous than lemmas

A particularly risky shape is:

```lean
noncomputable def data :
    TypeContainingHugeProofCarryingInstances :=
  value
```

because value-side proof abstraction can change nested proof expressions.

Lemmas about an already-named object are often cheap.

Practical rule:

> Put abstraction boundaries around data-valued constructions first; then prove lemmas about the named result.

---

## 16. Prefer heavy structures as hypotheses when mathematically honest

Compare:

```lean
def foo : Something (inferInstance : HugeStructure D) := ...
```

with:

```lean
def foo [h : HugeStructure D] : Something h := ...
```

A hypothesis is one free variable.

A concrete synthesized instance can contain sheafification proofs, localization choices, monoidal coherence data, derived-category constructions, and resolution proofs.

If the definition is genuinely polymorphic in the structure, passing it as a hypothesis is often both mathematically cleaner and kernel-friendlier.

---

## 17. Shortcut instances `:= inferInstance` are not free

A wrapper:

```lean
instance : HugeStructure D := inferInstance
```

helps synthesis, but can expose the entire synthesized body to kernel conversion if the wrapper is transparent.

Possible alternatives:

- keep the structure abstract as a parameter;
- name the construction it acts on;
- use `@[no_expose]` if downstream defeq should not inspect the implementation;
- avoid unnecessary wrapper instances.

---

## 18. When `@[no_expose]` is appropriate

Use it when:

> the implementation body should not participate in downstream definitional equality.

Interpretation:

- speedup + success: good abstraction boundary;
- immediate defeq failure: the API relied on the body;
- no change: the bad comparison occurs before reaching that definition.

`@[no_expose]` does **not** solve two already-different closed instance expressions embedded in the two sides of a comparison.

---

## 19. Instance priority is usually not a kernel fix

Priority changes future synthesis.

It does not rewrite hidden instance arguments already embedded in imported theorem types, stored definitions, inferred value types, or declared types.

If the kernel compares two closed terms already constructed, changing priority is usually irrelevant.

---

## 20. Subterm timing when `Kernel.check` is slow

For:

```text
f a₀ ... aₙ
```

measure:

```text
Kernel.check(aᵢ)
Kernel.check(f)
Kernel.check(f a₀)
Kernel.check(f a₀ a₁)
...
```

The jump from one prefix to the next includes:

```text
checking a_k
+
proving inferred type(a_k) =?= expected domain
```

Recurse into the dominant argument.

---

## 21. Recursive kernel tracing when structural diff is insufficient

Instrument recursive `is_def_eq_core` only after cheaper tools fail.

Log slow calls:

```text
depth
elapsed
lhs head
rhs head
arity
```

Look for:

> the deepest slow pair whose smaller differing children are no longer expensive.

Then instrument `is_def_eq_args`, `lazy_delta_reduction_step`, or proof irrelevance only around that pair.

---

## 22. Distinguish deterministic timeout from OOM

### Deterministic timeout

Often means a deep, repeated reduction path.

### OOM / exit 137

Often suggests branching/fan-out:

```text
many proof mismatches
→ many proposition-type comparisons
→ many data-valued instance comparisons
```

Record the failure mode; it is diagnostic evidence.

---

## 23. Generic constructive remedy matrix

| Diagnosis | First constructive change |
|---|---|
| heavy instance tree exposed in declared type | name the mathematical object built from it |
| many proof-only differences from value vs type | create a named data boundary before the proof-laden expression |
| concrete instance slow, hypothesis fast | parameterize over the instance where honest |
| same-head abbrev unfolds instead of comparing args | try `@[reducible] def` |
| implementation should not be definitionally visible | try `@[no_expose]` |
| wrapper `:= inferInstance` exposes huge body | remove wrapper or replace with named/abstract structure |
| proof irrelevance spends time on proof types | stabilize proposition types and their instance arguments |
| one application argument dominates | recurse into that argument conversion |
| OOM from proof fan-out | reduce proof-carrying expressions inside declared types |
| abstract case fast, concrete case slow | inspect concrete instance expansion; keep abstract API intact if possible |

---

## 24. Recommended API design rules

1. **Prefer named constants applied to small arguments in declared types.**
2. **Keep proof-heavy synthesized structures inside definition bodies.**
3. **Name diagrams, functors, objects, and structure-valued constructions early.**
4. **Do not automatically add unfolding lemmas for performance boundaries.**
5. **Use structure hypotheses when the mathematics is genuinely parametric.**
6. **Treat `:= inferInstance` wrappers as real implementation choices.**
7. **Use `abbrev → @[reducible] def` only when tracing shows a reducibility problem.**
8. **Use `@[no_expose]` only when the implementation should be semantically hidden from defeq.**
9. **After a fix, test the real value, not only `sorry`.**
10. **After a fix, build downstream API to ensure the boundary remains intact.**

---

## 25. Fast triage workflow for the next timeout

For a new difficult timeout:

1. Record baseline wall time.
2. Run with `debug.skipKernelTC`.
3. Restate the same type as an `axiom`.
4. Put the suspicious type expression in value position at `Type _`.
5. Replace the largest concrete instance by a hypothesis.
6. Replay:
   ```text
   Kernel.check(type)
   Kernel.check(value)
   Kernel.isDefEq(inferred, declared)
   ```
7. If `isDefEq` is slow:
   - run `Expr.equal`;
   - run structural diff immediately.
8. If minimal differences are mostly proofs:
   - inspect `abstractNestedProofs`;
   - identify proof-heavy instance expressions exposed in the declared type;
   - introduce a named boundary.
9. If differences are data terms:
   - find the deepest slow recursive defeq pair;
   - time its arguments;
   - inspect reducibility hints.
10. If same-head abbreviation behavior is confirmed:
    - test `@[reducible] def`;
    - optionally test a regular wrapper.
11. If an implementation body should not be visible:
    - test `@[no_expose]`.
12. Re-run with the real construction and downstream declarations.
13. Record what has been confirmed and ruled out.

---

## 26. Suggested diagnostic report template

```text
Environment
-----------
Lean:
Lean commit:
mathlib:
special options:
machine:

Baseline
--------
normal:
skipKernelTC:
failure mode: deterministic timeout / OOM / manual kill

Three discriminators
--------------------
same type as axiom:
expression in value position:
heavy instance replaced by hypothesis:

Kernel split
------------
Kernel.check(type):
Kernel.check(value):
Expr.equal inferred declared:
Kernel.isDefEq:

Structural diff
---------------
minimal differing positions:
proof-only?:
generated _proof_k constants?:
data-valued differences?:

Size
----
shared DAG size:
sizeWithoutSharing:

Diagnostics
-----------
top unfolded declarations:
top def_eq entries:
opaque bodies attempted:

Slow-pair trace
---------------
depth:
elapsed:
lhs head:
rhs head:
argument timings:
reducibility hints:

Interventions
-------------
named abstraction boundary:
instance as hypothesis:
abbrev -> @[reducible] def:
@[no_expose]:
regular wrapper:
custom kernel heuristic:

Conclusion
----------
Confirmed:
Ruled out:
Still open:
Chosen fix:
Why this fix is structurally appropriate:
```

---

## 27. Lessons from the successful `derivedCompletionCone` fix

The important observations were:

- the declaration timed out even with `sorry`;
- the same type as an `axiom` was fast;
- the same expression in value position was fast;
- `Kernel.check(type)` and `Kernel.check(value)` were milliseconds;
- only final `Kernel.isDefEq` was pathological;
- structural diff found many minimal differences, all proofs;
- the differences came from nested-proof abstraction on the value side;
- those proofs lived inside large concrete instance expressions;
- replacing the concrete derived monoidal instance by a hypothesis improved performance;
- naming the diagram completely removed the timeout;
- the real intended term then compiled in seconds;
- an `rfl` unfolding lemma recreated the timeout.

This establishes a reusable lesson:

> When proof-heavy instance expressions occur directly in the declared type of a data definition, naming the mathematical object they construct can be more effective and more robust than any transparency or reducibility tweak.

---

## 28. Final principle

The most useful question for a hard kernel timeout is often not:

> “Which low-level definition is slow?”

but:

> **“Which implementation-heavy or proof-heavy expression is unnecessarily visible in this declared type, and can I replace it with a stable named boundary before the kernel is asked to compare it?”**

A good fix prevents the expensive comparison from being created at all.
