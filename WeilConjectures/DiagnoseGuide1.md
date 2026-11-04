# Lean 4 Performance: A Systematic Diagnostic and Remediation Guide

**Scope:** Elaboration, asynchronous tasks, kernel type checking, definitional equality, and memory consumption  
**Reference environment for the case studies:** Lean / Mathlib v4.33.1  
**Audience:** Lean developers and coding agents debugging hard performance regressions

This guide combines lessons from kernel timeout investigations and a later elaboration/kernel performance study. Case studies emphasize the **reusable failure mechanism and repair**, rather than project-specific implementation details or benchmark status.

> **Core rule:** Identify the costly *phase*, then the smallest costly *check or conversion*, then the highest-level *abstraction boundary* that avoids creating that check. Optimize the expression the kernel sees, not merely the source proof script.

The goal is to make a declaration compile with ordinary kernel checking, preserve its intended semantics and downstream API, and reduce total elapsed time, CPU use, and peak memory. Diagnostic uses of `sorry`, `axiom`, or `debug.skipKernelTC` are **not** fixes.

---

## 1. Mental model: where the work happens

For a typical declaration:

```lean
theorem foo : Target := by
  ...
```

think of the overall pipeline as:

```text
parse / macro expansion
  -> elaborate declaration signature (universes, implicits, instances)
  -> elaborate proof or definition body (tactics, metavariables, constraints)
  -> finalize expression / abstract nested proofs / prepare declarations
  -> kernel: check declared type
  -> kernel: infer/check value and application arguments
  -> kernel: reconcile inferred type with declared type using defeq
  -> checked environment / downstream declarations
```

This is a *logical* decomposition, not a guarantee of a single sequential execution trace. Lean may elaborate proofs and kernel-check declarations asynchronously; generated auxiliary proofs (e.g. `_proof_17`) can be separate kernel-checked declarations.

For kernel diagnosis, use the conceptual model:

```text
Kernel.check(DeclaredType)
Kernel.check(value) -> InferredType
Kernel.isDefEq(InferredType, DeclaredType)
```

**Do not assume the last `isDefEq` is always the expensive part.** `Kernel.check(value)` itself checks applications, performs local domain conversions, and may recurse into costly projections. The `isDefEq` calls also depend on kernel state and context, not just the printed pair of expressions.

### Three distinct costs

| Symptom | Possible cause | First question |
|---|---|---|
| Slow elaboration, even with kernel skipped | Tactics, meta-level defeq, typeclass synthesis, metavariable instantiation, expression building | Which elaborator step dominates? |
| Kernel check slow, elaboration fast | Application conversion, value-vs-type defeq, reduction/projection path, proof abstraction | Which **kernel check** triggers the cost? |
| Large RSS / OOM | Repeated unfolding, large expression trees, cache or proof-comparison fan-out; sometimes elaborator allocations | Does memory rise in elaboration or kernel? |

A single structural mistake can affect all three. For example, hiding a huge instance tree behind a stable named data boundary can avoid repeated elaboration, expensive kernel conversions, and memory blow-up.

**Async warning:** `Elab.async -> elaborating proof of ...` identifies a task/snapshot, not a proof that tactic elaboration consumes the reported time. Kernel checking and waiting on dependencies may be accounted for in or around an async proof task. Confirm with synchronous benchmarks and per-declaration kernel traces.

---

## 2. Establish an honest baseline

Record Lean/Mathlib versions, git revision, imports, Lake options, hardware, number of parallel builds, and whether the machine is under load. Reproduce the problem in a scratch copy, initially without changing declarations.

Typical Linux benchmark:

```bash
lake env lean --version
/usr/bin/time -v lake env lean \
  -DElab.async=false \
  -Ddebug.skipKernelTC=false \
  -Dtrace.profiler=true \
  -Dtrace.profiler.threshold=500 \
  Bench.lean 2>&1 | tee bench.log
```

Pass any relevant `leanOptions` from `lakefile.toml` when invoking `lake env lean` directly. The `trace.profiler.threshold` unit is milliseconds in the normal time-measuring mode. For clean whole-file timing, rerun without trace instrumentation.

Collect **three different quantities**:

1. **Wall time:** user-visible delay; sensitive to machine load and waiting.
2. **CPU user/system time:** useful when external CPU contention makes wall time noisy; not an exact sum of per-declaration trace times.
3. **Peak RSS:** identifies memory-related regressions and possible OOM risk.

Run expensive variants **sequentially**. Repeat promising variants, preferably under comparable load. A variant that improves a single declaration but transfers the same cost into a helper or imported module is not a complete optimization.

### Optional 2 × 2 triage

For a representative file with no overriding local options:

```bash
for async in true false; do
  for skip in false true; do
    echo "async=$async skipKernelTC=$skip"
    /usr/bin/time -f 'wall=%e user=%U sys=%S rss=%M KB' \
      lake env lean \
        -DElab.async=$async \
        -Ddebug.skipKernelTC=$skip \
        Bench.lean
  done
done
```

| Pattern | Working conclusion |
|---|---|
| Kernel enabled slow; skipped fast; async setting barely matters | Primarily kernel checking |
| Async mode disproportionately slow | Investigate scheduling, dependencies, parallel contention |
| Both kernel-on and kernel-off slow | Elaboration or mixed cost |
| `skipKernelTC` helps only partially | More than one bottleneck |

`debug.skipKernelTC` deliberately bypasses part of the trusted validation path; only use it in isolated diagnosis. Never commit it as a performance solution.

---

## 3. Locate the declaration and the kernel phase

### 3.1 Profile before editing

```bash
lake env lean -DElab.async=false \
  -Dprofiler=true -Dprofiler.threshold=50 Bench.lean

lake env lean -DElab.async=false \
  -Dtrace.profiler=true -Dtrace.profiler.threshold=500 Bench.lean
```

Find `type checking` versus `elaboration` and individual `[Kernel] typechecking declarations [...]` entries. Be alert to generated `_proof_n` theorems and keep their costs separate from the parent definition.

Kernel and elaborator diagnostics can be useful independently:

```bash
lake env lean -DElab.async=false \
  -Ddiagnostics=true -Ddiagnostics.threshold=1 Bench.lean
```

The kernel's `unfolded declarations` counter may expose a recurring expansion chain. **The most-unfolded low-level declaration is not necessarily the cause.** A high-level conversion can trigger millions of routine library unfolds; locate that conversion before modifying the library hierarchy.

### 3.2 Three cheap discriminators

**Type-only control:** preserve the slow declared type, remove the value.

```lean
-- Diagnostic only
axiom foo_type_only (x : X) : HugeType x
```

Fast suggests the type itself is cheap to check; slow suggests the type already triggers an expensive check. Remove the axiom from the final patch.

**Expression in value position:**

```lean
-- Diagnostic only; adapt the universe as needed
def probe (x : X) : Type _ := HugeType x
```

This helps distinguish forming/checking an expression from checking a larger declaration whose type contains it.

**Replace a concrete heavy structure by a hypothesis:**

```lean
-- Diagnostic only; must remain mathematically meaningful
variable [h : HugeStructure D]
```

If this is dramatically faster than a concrete synthesized instance, that instance expression is amplifying the conversion. This is especially relevant for derived categories, monoidal categories, sheaves, localizations, and proof-carrying structures. A fast `#synth` does **not** imply kernel comparison of two concrete instance expressions is cheap.

### 3.3 Replay kernel phases (advanced)

On a scratch declaration initially introduced with kernel checking skipped, use a version-appropriate command elaborator / metaprogram to inspect its stored value and type, then time the operations independently. The following is adapted from the earlier diagnostic guide; verify the API against your Lean version:

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
  logInfo m!"Expr.equal: {Expr.equal inferredType declaredType}"

  let t2 ← IO.monoMsNow
  let r ←
    match Kernel.isDefEq env lctx inferredType declaredType with
    | .ok r => pure r
    | .error _ => throwError "Kernel.isDefEq failed"
  let t3 ← IO.monoMsNow
  logInfo m!"Kernel.isDefEq: {r}, {t3 - t2} ms"
```

For potentially nonterminating runs, write progress to a file and **flush it**: output from `run_cmd`/elaboration may be buffered until the command completes. Consider separately checking the declared type. Standalone replay has a fresh/different kernel state; it may have radically different timing from the check embedded in a full declaration.

**Interpretation:**

- `Kernel.check(value)` slow → bisect *application arguments and their expected domains*, structure constructors, or projection applications.
- Value check fast, final `Kernel.isDefEq` slow → compare inferred and declared types structurally immediately.
- Both fast in isolation but declaration slow → check kernel context/order, generated proof abstraction, and whether the replay reproduces the exact stored expressions.

---

## 4. Structural diff, not pretty-print equality

`pp` output may conceal different universe levels, implicit arguments, instance terms, auxiliary proof constants, beta redexes, or object representations. A pair of types that *prints identically* may be dramatically different to kernel defeq.

Compare with `Expr.equal`; recursively report the **smallest differing subterms**. The earlier guide used the following sketch:

```lean
partial def diffs (path : String) (a b : Lean.Expr) :
    Array (String × Lean.Expr × Lean.Expr) :=
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

This is a *diagnostic sketch*, not a full binder-aware, alpha-equivalence-aware structural comparison. For `Expr.fvar` differences, verify matching binder contexts. Normalize universe levels where appropriate; do not mistake syntactic `max` differences for intrinsically costly defeq.

Interpret the diff **by category**, not merely by count:

| Diff pattern | Next investigation |
|---|---|
| Many proof-only differences, especially `_proof_n` | Nested-proof abstraction and proof irrelevance |
| Same high-level constant, different arguments | Kernel hint/argument-congruence behavior; time each argument pair |
| Different high-level heads under a projection | Compare at the unprojected level; try explicit equality transport |
| Different hidden instances and universes inside a large binder type | Reuse a stable named proposition/interface head; reconstruct exact binder type |
| Huge data expression directly in a declared type | Named data boundary; abstract over structure if sound |

Diff counts such as “726 hidden differences” are evidence that the kernel sees different expressions, **not** proof that each difference costs time.

---

## 5. Top-down bisection when the kernel check is slow

Start from the highest-level expensive declaration and descend only when an experiment points into a subterm.

1. Temporarily replace the declaration body with an appropriately typed `sorry` (mind downstream effects of replacing a `def`).
2. Replace *one top-level proof component or data argument at a time* with a typed `sorry`.
3. For applications, time successive prefixes `f`, `f a₀`, `f a₀ a₁`, ... with the correct dependent types/context.
4. If the final `exact h` is expensive, replace **only** the final conversion. Preserve construction of `h`.
5. Recursively bisect the smallest expensive expression/type pair. Stop descending once all children are cheap.

A prefix-cost jump means the kernel may be paying for *both* `check(aᵢ)` and `type(aᵢ) ≡ expectedDomainᵢ`. Do not attribute it solely to checking `aᵢ`.

### Controlled cross-expression HEq probes

For an expensive pair `a`, `b` suspected to be definitionally equal:

| Probe | Type | Proof | What it controls |
|---|---|---|---|
| P1 | `HEq a a` | `HEq.refl a` | Checking `a` / self case |
| P2 | `HEq b b` | `HEq.refl b` | Checking `b` / self case |
| P3 | `HEq a b` | `HEq.refl a` | Cross-expression conversion |
| P4 | `HEq a b` | `sorry` | Checking the proposition itself |
| P5 | `type(a) = type(b)` | `Eq.refl` | Conversion of the expression types |

Generate separate auxiliary theorems (for example with `Lean.Meta.mkAuxTheorem`, `cache := false`), ideally each in its own Lean process. P4 is a diagnostic control, never a final theorem. If P1/P2/P4/P5 are cheap and P3 extremely expensive, the cross-expression conversion is strongly implicated. If P1 itself is slow, the ordinary typing of `a` must also be examined.

**Reusable observation:** In a real `NatTrans.app` case, the self-checks, proposition check, and type comparison were cheap, while only P3 took minutes and caused a large memory increase. This isolates *cross-expression conversion*, not merely the cost of constructing or typing a large expression.

---

## 6. Failure patterns and their specific remedies

### Pattern A — Expensive conversion *beneath* a projection

**Shape:**

```lean
(τ₁.app X).app Y   -- or some large structure field / composition projection
(τ₂.app X).app Y
```

The transformations `τ₁` and `τ₂` can be cheap to compare directly, but comparing their projections may force the kernel to evaluate constructors, structures, instances, or derived-category operations. Large counts for unrelated-looking low-level definitions can be fallout from this path.

**Do not try to fix the deepest unfolded definition first.** Move the comparison *upstream of the projection* using a propositional equality plus transport.

In the successful `Comparison.lean` fix, a generic lemma had the following shape:

```lean
-- Schematic; use actual category imports and universe parameters
lemma app_app_comp_of_eq
    {F G : C ⥤ D ⥤ E} {τ : F ⟶ G} {X : C} {Y : D}
    {f : (G.obj X).obj Y ⟶ Z}
    {k : (F.obj X).obj Y ⟶ Z}
    (h : (τ.app X).app Y ≫ f = k)
    (σ : F ⟶ G) (hσ : σ = τ) :
    (σ.app X).app Y ≫ f = k :=
  hσ ▸ h
```

Then instead of a costly final `exact h`, use:

```lean
exact app_app_comp_of_eq h
  (leftDerivedUpperStarTensorComparison A g) rfl
```

The `rfl` now compares *natural transformations themselves* (cheap in this case) rather than two expressions under `NatTrans.app` (very expensive). The equality eliminator supplies the component-level statement without making the kernel rediscover the projection-level defeq.

**Boundary type:** *propositional equality / proof-term structure*, not opacity. Adding an unrelated lemma is insufficient; the lemma must move the actual comparison to the cheaper level.

**Failure checks:** the equality theorem might itself be expensive; transport or a subsequent `rw` may recreate the original conversion. Measure all generated proof constants and the original declaration.

### Pattern B — Complex binder proposition; hidden argument mismatch

**Shape:** a generic constructor such as `ofLaxSquare` expects a long proposition `P_expected`, while a mathematically correct theorem has type `P_actual`. The difference is hidden instances, universe paths, generated `_proof_n` constants, object/functor representations, and possibly beta redexes. Conversion inside a large application can be far slower than checking the same apparent pair in a standalone theorem.

**Remedy:** name the expected proposition with a **regular `def`**, and make the consumer accept that named proposition directly. Supply a small bridge theorem with the named type.

The successful construction had the schematic shape:

```lean
-- Regular `def`, not `abbrev`.
def LaxSquareHδ (δG : ...) (e : ...) : Prop :=
  ∀ a b, ...  -- original square-compatibility statement

noncomputable def ofLaxSquareHδ
    ... (hδ : LaxSquareHδ δG e) ... : G.OplaxMonoidal :=
  Functor.OplaxMonoidal.ofLaxSquare δG e he hδ S hS hμ

lemma leftDerivedUpperStarTensorComparison_laxSquareHδ :
    LaxSquareHδ (leftDerivedUpperStarTensorComparison A g)
      (fun a => (g)^*[A].leftDerivedFunctorCounit.app a) :=
  leftDerivedUpperStarTensorComparison_app_app_comp A g
```

Now the outer kernel check can compare two `LaxSquareHδ ...` applications by their arguments first. This may avoid unfolding the immense underlying proposition. A **plain `def`** provided the desired kernel regular hint in the measured case; the analogous `abbrev` experiment kept the original several-hundred-second cost.

**Why this works:** for equal-height *regular* definition heads, the kernel's lazy delta checker can try argument congruence before unfolding. Kernel reducibility hints are distinct from elaborator `@[reducible]`/`@[irreducible]` attributes; changing an elaborator transparency attribute is not the same experiment.

**Boundary type:** *named proposition / binder interface*, combined with a theorem boundary. It need not hide a definition body. It is not a universal guarantee: argument comparison must be cheap and successful.

**Important nuance:** the same apparent conversion can be cheap in a standalone theorem yet very expensive inside a large application. Kernel checking order or cache state may matter, but that mechanism remains a hypothesis; the practical remedy is to place the conversion behind a correctly typed theorem/interface boundary.

### Pattern C — `abstractNestedProofs` and proof-only type divergence

Lean may replace proofs nested in a definition's *value* with auxiliary theorems such as `Foo._proof_1`, including proofs occurring in type-valued subexpressions. A declared type may retain differently elaborated or unabstracted proof expressions:

```text
DeclaredType: BigType (... rawProof₁ ...) (... rawProof₂ ...)
InferredType: BigType (... Foo._proof_1 ...) (... Foo._proof_2 ...)
```

The kernel may need to compare the types of proof terms before exploiting proof irrelevance. Those proposition types can depend on **data-valued** class instances (`MonoidalCategory`, `HasDerivedCategory`, etc.), creating recursive comparisons of large proof-carrying structures.

**Diagnostic signs:** declared type fast, value fast, final `isDefEq` enormous; structural diff dominated by proof constants; possible deterministic timeout or OOM.

**Remedy:** give the *mathematical data object* a stable name **before** it appears inside downstream declared types:

```lean
noncomputable def completionDiagram (K : D) : ℕᵒᵖ ⥤ D :=
  bigFunctor ⋙ tensorLeft K

noncomputable def completionCone (K : D) :
    Cone (completionDiagram K) :=
  ...
```

Now downstream types use `completionDiagram K`, not the entire implementation tree. As the earlier `derivedCompletionCone` case showed, a convenience unfolding lemma proved by `rfl` can **recreate** the original timeout by forcing kernel comparison against freshly elaborated proof expressions. Do not puncture a successful boundary simply to restore old definitional equalities.

**Boundary type:** *named data construction in declared types*. Sometimes parameterizing over a genuinely variable structure is better than committing to a giant concrete instance.

### Pattern D — Same-head abbreviation prefers unfolding

**Shape:** `f a₀ ... aₙ =?= f b₀ ... bₙ`, with cheap argument conversions but costly unfolding of `f`.

Try changing a relevant abbreviation-like API into a regular definition:

```lean
-- Before
abbrev Foo args := hugeConstruction args

-- Diagnostic candidate when elaborator transparency is needed
@[reducible] def Foo args := hugeConstruction args
```

Or use an ordinary `def` wrapper if the elaborator does not need `@[reducible]`. Check that both sides share the **same named head** at the conversion site. Changing a distant abbreviation that does not occur on the slow path will not help.

**Boundary type:** *kernel same-head congruence / reduction-order hint*, not true opacity.

### Pattern E — Heavy concrete structures inside types

Compare:

```lean
-- Concrete instance term embedded in the type
Something (inferInstance : HugeStructure D)

-- Abstract / parametric API
variable [h : HugeStructure D]
-- Something h
```

When mathematical meaning permits abstraction, prefer a structure parameter or a named data object. An `instance := inferInstance` wrapper can speed elaborator synthesis yet still expose a huge body to kernel conversion. Instance priorities influence future synthesis but do **not** retroactively change instance expressions stored in imported theorem types.

### Pattern F — Module exposure boundary (`@[no_expose]`)

Use the module system and `@[no_expose]` only when the implementation should genuinely be *unavailable* for downstream definitional reduction. It is not a general local reducibility attribute, and it has no useful such effect in non-`module` files. A true boundary needs a defining module, public signature, and a consumer using the appropriate import visibility (not `import all` to recover hidden bodies).

Three diagnostic outcomes:

- **Speedup and success:** the hidden body was unnecessary and removing it stopped expensive reduction.
- **Immediate defeq failure:** downstream code relied on unfolding the implementation; add carefully designed interface theorems or reconsider the boundary.
- **No improvement:** the expensive comparison is elsewhere; don't force a module refactor.

**Reusable negative result:** moving a definition across modules may alter generated-proof sharing, and hiding its body may invalidate existing `rfl` proofs without addressing the actual expensive conversion. Prefer a shared regular definition or an explicit higher-level equality when those suffice; reserve `no_expose` for a genuine API boundary.

**Preference:** choose the *least invasive boundary that avoids the bad comparison*. Do not reach for kernel-level irreducibility or module hiding when regular wrappers and explicit equality transport already work.

---

## 7. Why some intuitive fixes fail

| Attempt | Why it may fail | Better diagnostic |
|---|---|---|
| Add a local `have` or `by exact` wrapper | New proof syntax may not change the outer inferred-vs-expected type comparison | Inspect elaborated argument's type and expected binder type |
| Split a huge proof arbitrarily | Cost just moves to another helper theorem | Measure **sum** of all newly generated/checking declarations |
| Rewrite or `delta` a large definition | Forces more projection-level reduction | First compare unprojected objects via an equality theorem |
| Use `abbrev` to give a long proposition a name | Abbreviation can be unfolded eagerly by kernel | Test ordinary `def` with same-head comparison |
| Make a definition `@[no_expose]` | Downstream `rfl`/`inferInstanceAs` may fail; the bad conversion can remain | Test true module boundary and required interface lemmas |
| Change low-level hom-group definitions | They may be downstream unfold victims, not triggers | Bisect from the **top-level expensive conversion** |
| Change instance priority | Does not rewrite already elaborated hidden instances | Compare the actual stored `Expr`s |
| Compare pretty-printed types | Hidden universe/instance/proof arguments may differ | Use `Expr.equal` + structural diff |
| Assume standalone `HEq` time equals in-situ time | Kernel state, ordering, or context differs | Benchmark both standalone and original declaration |
| Use `sorry`/`skipKernelTC` as a fix | Avoids trusted checking and may break downstream definitions | Restore full checking and verify axioms |

---

## 8. Measurement pitfalls: context, sharing, and memory

### 8.1 Kernel context matters

When building a large application `f a₀ ... aₙ`, the kernel checks preceding arguments before reaching `aₖ`. Memoized failed congruence checks, WHNF caches, local environments, or check order can affect later operations. **Treat the exact causal role of any specific cache as a hypothesis unless traced.**

For a critical binder argument, extract its expected domain from the *actual elaborated application* by instantiating preceding `Π` binders with the actual arguments. Preserve universe parameters and bound variables. Compare:

- raw instantiated binder type (without beta-reduction);
- beta-normalized binder type;
- actual type of the argument;
- type of any auxiliary bridge theorem at the use site.

An exact binder-type theorem can turn an expensive in-situ conversion into a cheap standalone theorem check. However, this is **not** equivalent to writing `have h := ...`; the auxiliary theorem's **declared type** must line up with the consumer's binder interface.

### 8.2 Expression size and sharing

Observe shared DAG size as well as `sizeWithoutSharing` when available; a seemingly short proof can contain large terms or repeated substructures. Still, a tiny expression can trigger an enormous definitional reduction. Use size diagnostics **after** confirming which conversion is expensive, rather than treating term length as the default explanation.

### 8.3 Memory as corroborating evidence

A large RSS jump in a *cross-expression HEq probe* while self-check probes stay fast supports expensive reduction/defeq as a common cause of CPU and memory pressure. It does **not** by itself identify the allocation source.

OOM or exit code 137 is suggestive but not definitive; confirm with Linux OOM/cgroup diagnostics. Distinguish deterministic kernel timeouts from memory-pressure terminations. Profile with and without trace overhead, and compare peak RSS only under similar conditions.

---

## 9. Case studies: reusable diagnostic lessons

These cases are deliberately summarized by **symptom → mechanism → effective intervention → lesson**. The general methods and code patterns appear in Sections 3–8.

### Case A — Proof-heavy data embedded in a declared type

- **Symptom:** The declared type and value check quickly in isolation, but their final definitional equality is extremely slow; structural diff reveals many generated proof-constant mismatches.
- **Mechanism:** Nested-proof abstraction and separately elaborated, proof-carrying instance expressions make the kernel compare deep proposition types.
- **Effective intervention:** Name the underlying diagram or data construction once, then use that named constant in subsequent declared types. Avoid convenience unfolding lemmas that recreate the mismatch.
- **Lesson:** **Stabilize a large data object at the type boundary, not just a proof about it.**

### Case B — Definitional equality under a natural-transformation projection

- **Symptom:** A final `exact h` triggers a very slow conversion although the natural transformations themselves are cheap to compare. Only the cross-expression `HEq` probe is slow.
- **Mechanism:** Comparing applications of differently represented natural transformations can force deep projection-level reduction.
- **Effective intervention:** Prove an equality of the enclosing natural transformations first; use propositional equality transport (`▸` / `Eq.rec`) to obtain the component statement.
- **Lesson:** **Move equality reasoning above the expensive projection.** An arbitrary auxiliary lemma is not enough unless it changes the kernel's obligation.

### Case C — Complex proposition passed through a generic constructor

- **Symptom:** Passing a theorem to a deeply dependent binder triggers a slow type conversion, while the same conversion in an isolated theorem is relatively cheap. The types print similarly but differ in hidden parameters.
- **Mechanism:** Expanded binder propositions expose independently elaborated instances, universes, and generated proofs. A plain `abbrev` wrapper still unfolds too eagerly.
- **Effective intervention:** Name the proposition with a **regular `def`**, make the consumer accept that named type, and prove a small bridge theorem.
- **Lesson:** **A stable regular-definition head can be a more effective boundary than opacity or another proof wrapper.**

**Shared lesson:** Reduce the need to compare expanded implementations. Prefer the least invasive named interface or equality transport that makes the relevant kernel check cheap; verify the total cost of all new declarations, not only the original slow one.

---

## 10. Recommended diagnostic decision tree

```text
Slow Lean declaration / high memory
  |
  +-- Baseline: async × skipKernelTC; wall, CPU, RSS
  |
  +-- Slow with kernel skipped?
  |      YES -> profile elaborator: tactics, typeclasses, metavariables,
  |             elaborator defeq, proof construction; look for shared
  |             high-level data/instance boundaries.
  |      NO  -> profile per-declaration kernel checking.
  |
  +-- Kernel slow in which declaration (incl. _proof_n)?
  |      |
  |      +-- Does replacing body or one typed component isolate it?
  |      +-- Does replacing only final exact isolate a conversion?
  |      |
  |      +-- Kernel.check(value) slow?
  |      |       -> prefix/argument bisection, expected domain conversions,
  |      |          projection/structure checking.
  |      |
  |      +-- Final inferred-vs-declared defeq slow?
  |              -> Expr.equal, structural diff, controlled HEq probes.
  |
  +-- Minimal expensive pair found
  |      |
  |      +-- Under NatTrans.app / structure projection?
  |      |       -> equality at the higher-level object, transport.
  |      |
  |      +-- Huge expected binder proposition, many hidden diffs?
  |      |       -> regular def naming proposition + exact binder bridge.
  |      |
  |      +-- Many abstracted proof-only diffs in declared types?
  |      |       -> named data/object boundary; avoid unfolding API lemmas.
  |      |
  |      +-- Same-head abbreviation unfolding unnecessarily?
  |      |       -> regular def / optionally @[reducible] def.
  |      |
  |      +-- Concrete proof-heavy instance tree?
  |              -> genuine structure parameter or named data object.
  |
  +-- Only if the implementation should be hidden across modules:
  |      -> test actual module boundary + @[no_expose] + interface lemmas.
  |
  +-- Rerun real theorem/definition with ordinary kernel checking;
         account for all auxiliary proof/module costs, peak RSS,
         correctness, axioms, and downstream builds.
```

**Escalation rule:** Instrument kernel C++ (`is_def_eq_core`, `lazy_delta_reduction_step`, projection handling, proof irrelevance) only if top-down Lean-level probes cannot isolate a useful high-level boundary. Deep tracing should record depth, duration, heads, arity, and expensive argument pairs, with bounded logging to avoid altering performance drastically.

---

## 11. Fix selection matrix

| Diagnosis | First thing to try | Confirmation of success |
|---|---|---|
| `exact h` triggers costly projected-term defeq | Higher-level Eq theorem + `Eq.rec`/`▸` transport | Original check cheaper; helper cheap; no new expensive conversion |
| Consumer has complex `hδ`-like binder proposition | Regular `def` for proposition + wrapper consumer + bridge theorem | Same-head argument conversion; total kernel cost falls |
| `abbrev` head unfolds despite cheap argument equality | Ordinary `def`, or `@[reducible] def` if elaborator needs transparency | Both sides share regular head; fewer deep unfolds |
| Many proof-only inferred/declared diffs | Named heavy data object in declared type | Final `isDefEq` collapses without costly unfolding lemma |
| Concrete instance is huge; abstract hypothesis cheap | Parameterize mathematically honest structure | Same type family, cheap instance-variable comparisons |
| Expensive application argument | Prefix bisection and exact domain extraction | Narrower expensive argument identified |
| Expensive body must be hidden from importers | `module` + carefully scoped `@[no_expose]` | Downstream has working characterizing API; build succeeds |
| High RSS correlates with specific defeq probe | Avoid the comparison at high level | CPU and peak RSS improve together |
| Async proof task looks stuck | Turn async off, compare kernel traces and dependency waits | Time assigned to real phase/declaration |

---

## 12. Validation and release checklist

A performance patch is complete only when all of these are satisfied:

- [ ] Original theorem statements/data types and mathematical meaning preserved (or deliberate API changes documented).
- [ ] No new `sorry`, `sorryAx`, diagnostic axioms, `debug.skipKernelTC`, or weakened checker settings are present.
- [ ] Normal kernel checking succeeds; use `#print axioms` on critical declarations where helpful.
- [ ] All newly generated `_proof_n` declarations and helper lemmas are included in total performance accounting.
- [ ] Both isolated microbenchmark **and** original full file improve.
- [ ] Peak RSS and CPU time improve or at least do not regress materially.
- [ ] A changed module/exposure boundary is checked using proper ordinary imports and full downstream builds.
- [ ] Avoid gratuitous unfolding lemmas that recreate the original bad conversion.
- [ ] Benchmarks are reproducible under a known toolchain, with options, commands, and load recorded.
- [ ] The chosen solution is simpler than alternatives providing no measurable benefit.

Do not conflate an instrumented scratchpad experiment (`run_meta`, `addDecl`, kernel-unchecked probes) with a maintainable source-level solution. A fast meta-generated declaration is useful evidence, but the final repair should be expressed as an ordinary source-level interface and checked normally.

---

## 13. Coding-agent workflow and report template

### Agent instructions

1. Preserve a clean baseline and original source file; place variants in scratch files or a dedicated worktree.
2. Run a small number of controlled experiments in sequence; avoid brute-force parallel Lean builds.
3. Record per-declaration kernel time *and* whole-file wall/CPU/RSS.
4. Use typed `sorry` only to **localize**, and restore real proofs before concluding.
5. Work **top-down**. Do not descend into the most frequently unfolded library instances unless a probe proves they are the minimal expensive pair.
6. Once a successful high-level boundary is found, stop searching for lower-level reducibility hacks.
7. Report failed fixes, their error mode, and whether they transferred rather than removed cost.
8. End with a source-level patch, correctness checks, and any relevant import/API compatibility considerations.

### Report skeleton

```text
Environment
-----------
Lean, Mathlib, revision, machine/core count, RAM, load
Command line, lakefile options, profiler/diagnostic options

Baseline
--------
wall, user CPU, sys CPU, peak RSS
async/skipKernelTC matrix (if applicable)
slow declaration(s) and generated _proof_n checks

Phase localization
------------------
elaboration vs kernel
Kernel.check(declared type)
Kernel.check(value)
Kernel.isDefEq(inferred, declared)

Structural localization
-----------------------
Expr.equal, universe/instance/proof diff summary
smallest expensive subterm/type conversion
HEq P1–P5 controls, if conversion suspected
application-prefix/binder extraction, if applicable

Mechanism hypothesis
--------------------
projection? regular/abbrev head? proof abstraction?
concrete instance tree? context/cache? memory fan-out?
Which claims are proven by controls and which remain hypotheses?

Intervention comparison
-----------------------
variant -> what was changed, compilation status
per-declaration kernel / helper kernel / combined kernel
wall / user CPU / peak RSS
transferred cost or eliminated cost?

Validation
----------
normal kernel checking, no sorry/new axioms, #print axioms
full-file checking; import/exposure compatibility when relevant

Conclusion
----------
confirmed root cause and expensive pair
best abstraction boundary and why it works
remaining hotspots / open questions
```

---

## 14. Principles to remember

1. **The hottest unfolded library constant is often a victim, not the trigger.** Locate the highest-level conversion that exposes it.
2. **A lemma helps only when it changes the kernel's proof obligation.** Equality transport before a projection can be transformative; arbitrary proof splitting may not be.
3. **A named regular `def` can be a performance boundary without being opaque.** Same-head argument congruence can short-circuit huge definitions.
4. **A named *data* boundary and a named *proposition* boundary solve different problems.** Both stabilize the types kernel must compare.
5. **Proof irrelevance is not automatically cheap.** The proposition types of abstracted proofs may still contain enormous data-valued instances.
6. **Exact hidden arguments matter.** Pretty-printed equality is not syntactic equality; reconstruct expected binder types when necessary.
7. **The kernel's checking context matters.** A standalone 9 s conversion can cost hundreds of seconds within a large application; avoid diagnosing only from microbenchmarks.
8. **`no_expose` is an API visibility choice, not the default performance lever.** Test it only with a real module boundary and downstream builds.
9. **Measure total cost and RSS, not just one trace node.** A fix that transfers cost or adds module build overhead may be illusory.
10. **Prefer a stable high-level API over carefully tuned low-level unfolding.** Prevent the pathological comparison from arising in the first place.

> **Final question:** Which implementation-heavy or proof-heavy expression is visible at the exact point of an expensive kernel comparison, and what named interface or propositional equality can prevent the kernel from comparing its expanded form?

---

## 15. Technical references and provenance

**Project reports (user-provided):**

- Original *Lean Kernel Timeouts: Diagnostic and Remediation Guide* (especially the `derivedCompletionCone` case, `abstractNestedProofs`, and structural diff).
- *Kernel performance of `UpperStarMonoidal/Comparison.lean`: diagnosis report* (first round and top-down bisection).
- *Diagnosis report 1* (controlled HEq probes and exact binder-type auxiliary theorem).
- *Fixing report* (V1W solution, failed `abbrev` and module exposure variants, final performance comparison).

**Upstream references (consulted for mechanism descriptions):**

- Lean's `ReducibilityHints` documentation: <https://lean-lang.org/doc/api/Lean/Declaration.html>
- Kernel lazy delta reduction implementation: <https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp>
- Lean's module visibility and exposure documentation: <https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/>
- Lean trace profiler options: <https://github.com/leanprover/lean4/blob/master/src/Lean/Util/Trace.lean>
- Lean meta/kernel diagnostics: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Diagnostics.lean>

Implementation details are version-sensitive. The observed mechanisms and repair choices were studied with **Lean 4.33.1**; verify option names, kernel APIs, and performance behavior on the project's actual toolchain.
