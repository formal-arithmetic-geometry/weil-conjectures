# Lean 4 Kernel Performance — Next Experiments

## Goal

Investigate the two expensive kernel type conversions identified in the previous report, focusing on:

1. Validating whether the `HEq` probes genuinely measure expensive definitional equality.
2. Avoiding the expensive `hδ` argument conversion in `leftDerivedUpperStarOplaxMonoidal` by introducing an auxiliary theorem with an exact binder type.

Do not investigate lower-level `Preadditive` or hom-group definitions. Do not attempt the `NatTrans`-level equality refactoring (Target A) yet.

## Experiment 1: Validate the HEq Conversion Probe

### Background

The previous investigation found that comparing two natural transformations costs approximately 3.5 s, while comparing their applications under `NatTrans.app` costs approximately 280 s.

However, the `HEq` probe also involves kernel checking of the expressions themselves. We need to distinguish the actual cross-expression conversion cost from ordinary expression type checking.

### Procedure

Use the expensive pair `(a, b)` identified at `lhs.5.6` in the previous report:

```lean
-- a
NatTrans.app (leftDerived₂NatTrans ...) (Qh.obj K)

-- b
NatTrans.app (leftDerivedUpperStarTensorComparison A g) (Qh.obj K)
```

Construct four independent kernel-checking probes:

| Probe | Declaration type | Proof | Purpose |
|---|---|---|---|
| P1 | `HEq a a` | `HEq.refl a` | Baseline for checking `a` |
| P2 | `HEq b b` | `HEq.refl b` | Baseline for checking `b` |
| P3 | `HEq a b` | `HEq.refl a` | Cross-expression conversion |
| P4 | `HEq a b` | `sorry` | Baseline for checking the proposition itself |

Use the existing `Lean.Meta.mkAuxTheorem` infrastructure. Ensure that each probe is independently kernel-checked, with no cached auxiliary theorem reused across measurements.

Record whether each probe succeeds, its kernel checking time, and relevant diagnostics if available.

### Interpretation

- **P1/P2/P4 fast, P3 very slow:** Strong evidence that the cross-expression definitional equality is expensive.
- **P1 or P2 also slow:** Some cost comes from checking the expressions individually.
- **P4 slow:** Constructing or checking the proposition type itself is expensive.
- **P3 fast in isolation but slow in the original theorem:** Investigate differences in the exact elaborated expressions or checking context.

Do not assume that the reported 280 s represents pure `isDefEq` time until these controls are completed.

## Experiment 2: Exact Binder-Type Auxiliary Theorem for Target B

### Background

In `leftDerivedUpperStarOplaxMonoidal`, the kernel takes approximately 230–250 s to check the definition.

Replacing the `hδ` argument of `ofLaxSquare` with a typed `sorry` reduces this to approximately 2–4 s.

The previous report also found:

- The expensive argument is `leftDerivedUpperStarTensorComparison_app_app_comp A g`.
- All other elaborated arguments to `ofLaxSquare` are syntactically unchanged.
- An isolated conversion to a normalized expected type takes approximately 18.6 s.
- Wrapping the original argument in `by exact ...` does not improve performance.

The hypothesis is that the expensive conversion can be performed once in an auxiliary theorem, whose **declared type exactly matches the instantiated `hδ` binder type**.

### Step 1: Extract the Exact Binder Type

From the elaborated application of `ofLaxSquare`, extract the expected type of `hδ` after substituting all preceding arguments.

Pay special attention to:

- Implicit and instance arguments.
- Universe parameters.
- The actual elaborated expressions for `δG` and `e`.
- Beta-redexes introduced by `e := fun a => counit.app a`.
- Differences between the raw instantiated binder type and the elaborator-normalized type.

Compare the actual `Expr` structures, not just their pretty-printed representations.

### Step 2: Create an Auxiliary Theorem

Introduce an auxiliary theorem whose statement matches the instantiated binder type as closely as possible.

Schematic example:

```lean
private theorem delta_for_ofLaxSquare
    (A ...) (g ...) :
    P_binder := by
  exact leftDerivedUpperStarTensorComparison_app_app_comp A g
```

Here, `P_binder` must be replaced with the exact expected `hδ` type extracted in Step 1.

Then supply the new theorem directly:

```lean
-- Inside the original ofLaxSquare application:
hδ := delta_for_ofLaxSquare A g
```

Do not merely wrap the original argument in `by exact ...`, as that approach has already failed.

If necessary, test two versions:

- **B1:** Auxiliary theorem using the raw instantiated binder type.
- **B2:** Auxiliary theorem using the beta-normalized binder type.

For each version, inspect whether the resulting theorem constant's type is syntactically identical to the expected `hδ` type at the actual application site.

### Step 3: Benchmark the Result

Record separately:

| Measurement | Original | Auxiliary theorem variant |
|---|---|---|
| `delta_for_ofLaxSquare` kernel time | — | ? |
| `leftDerivedUpperStarOplaxMonoidal` kernel time | ~230–250 s | ? |
| Combined kernel time | ~230–250 s | ? |
| Peak memory | Baseline | ? |
| Kernel checking succeeds | Yes | ? |

Also record whether any additional conversion appears in generated auxiliary proofs.

### Interpretation

- **Auxiliary theorem ~20 s, oplax definition ~2–5 s:** Strong evidence that the expensive binder conversion has been successfully isolated and avoided at the application site.
- **Auxiliary theorem ~230 s, oplax definition fast:** The cost was only transferred, not eliminated.
- **Auxiliary theorem fast, oplax definition still slow:** The actual application still triggers a conversion. Inspect the elaborated theorem type against the instantiated binder type.
- **Raw and normalized variants behave differently:** Investigate how beta-redex placement affects kernel checking.

If no syntactically exact binder match can be constructed, report the smallest remaining `Expr` difference rather than making speculative changes to lower-level definitions.

## Benchmark Requirements

- Lean v4.33.1, existing project configuration.
- `Elab.async=false`.
- `debug.skipKernelTC=false`.
- Use kernel trace/profiler for per-declaration measurements.
- **Run benchmarks sequentially**, not five at a time as in the previous investigation.
- Preserve original definitions and proof logic except for controlled diagnostic changes.
- Use `sorry` only in diagnostic probes; final candidate solutions must pass ordinary kernel checking without introducing new axioms or `sorry`.

## Deliverables

Provide a concise Markdown report including:

1. The four HEq probe results and what they establish about conversion cost.
2. The exact instantiated `hδ` binder type and relevant structural differences.
3. Auxiliary theorem variants and their kernel checking times.
4. Combined runtime and memory comparisons.
5. Whether an effective abstraction boundary was found.
6. The smallest unresolved conversion or expression mismatch if the experiment fails.

**Priority:** Establish a reliable measurement of kernel conversion cost, then determine whether an exact-type auxiliary theorem can eliminate the expensive `hδ` conversion without simply moving its cost elsewhere.

Do not proceed to the separate Target A refactoring experiment yet.