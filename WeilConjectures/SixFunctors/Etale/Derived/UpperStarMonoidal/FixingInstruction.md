# Lean 4 Kernel Performance — Wrapper and `no_expose` Experiments

## Goal

Investigate whether we can eliminate the expensive kernel type conversions in:

- `leftDerivedUpperStarTensorComparison_app_app_comp` (\~200 s)
- `leftDerivedUpperStarOplaxMonoidal` (\~230 s)

The previous investigation suggests that expensive definitional equality occurs when comparing different representations of the same natural transformation under `NatTrans.app`.

**Our preferred approach is to introduce a suitable high-level wrapper and use `@[no_expose]` to establish a controlled unfolding boundary.**

Do not attempt `irreducible_def`, `opaque`, or changes to lower-level `Preadditive` infrastructure.

## Experiment 1: High-Level Natural Transformation Wrapper

### Hypothesis

The expensive conversion arises because the kernel compares:

```lean
(leftDerived₂NatTrans ...).app X
```

against:

```lean
(leftDerivedUpperStarTensorComparison A g).app X
```

Although these natural transformations are definitionally equal, comparing them under `NatTrans.app` triggers expensive unfolding.

A wrapper may allow both sides to use the same high-level expression, avoiding this conversion.

### Procedure

1. Identify the common natural transformation represented by the two expressions.
2. Introduce a named wrapper at the **natural transformation level**, before applying `NatTrans.app`.
3. Modify Target A to use this wrapper consistently wherever possible.
4. Preserve the mathematical content and theorem statements unless an explicit interface adjustment is required.
5. Benchmark the resulting kernel checking time.

Start with a regular `def` wrapper. Do not introduce module boundaries yet.

### Interpretation

- **Large improvement:** Syntactic alignment at the natural transformation level is sufficient.
- **No improvement:** The kernel is still unfolding the wrapper or encountering another expensive conversion.
- **Kernel type-checking failure:** Record the exact expressions and required conversions. Do not force unfolding merely to recover definitional equality.

## Experiment 2: `@[no_expose]` and Module Boundaries

### Hypothesis

Even with a shared wrapper, the kernel may unfold its definition during type checking.

Using the module system with `@[no_expose]` may prevent downstream kernel checks from expanding the wrapper into the expensive underlying construction.

### Procedure

1. Move the wrapper into a separate Lean module.
2. Ensure both the defining file and the consuming file use the `module` system.
3. Compare an exposed wrapper against a wrapper marked `@[no_expose]`.
4. Use ordinary `import`, not `import all`, in the consuming module.
5. Recheck Target A and, if promising, Target B.

Schematic structure:

```lean
-- ComparisonWrapper.lean
module

public import ...

@[expose] public section

@[no_expose]
noncomputable def comparisonWrapper (A ...) (g ...) :
    F ⟶ G :=
  -- Original natural transformation construction
  ...
```

For the exposed control variant, remove `@[no_expose]` while keeping the enclosing `@[expose]` section.

**Important:** `@[no_expose]` negates exposure; it is not a general-purpose irreducibility attribute. It can be redundant on definitions that are already unexposed, and it has no useful module-boundary effect in ordinary non-`module` files.

### Characterizing Lemmas

If the original proofs require unfolding the wrapper, introduce explicit characterizing lemmas in the defining module, where the body remains available.

For example:

```lean
theorem comparisonWrapper_eq (A ...) (g ...) :
    comparisonWrapper A g =
      originalComparison A g := by
  rfl
```

Then use these lemmas to connect representations explicitly rather than relying on expensive definitional equality beneath `NatTrans.app`.

The characterizing lemma itself must be kernel-checked, and its cost must be included in the benchmark.

Avoid rewriting in ways that simply recreate the original expensive conversion.

### Important Constraints

- Do not blindly apply `@[no_expose]` to existing definitions.
- Avoid hiding definitions required by downstream `rfl` or `inferInstanceAs` proofs without providing appropriate interfaces.
- If direct conversion fails after hiding a definition, this is useful diagnostic evidence.
- Keep the wrapper as high-level as possible.
- Do not descend into the hom-group or algebraic hierarchy.

## Benchmark Matrix

Measure each variant with `Elab.async=false` and `debug.skipKernelTC=false`.

| Variant | Wrapper                        | Exposure       |
| ------- | ------------------------------ | -------------- |
| V0      | Original code                  | Original       |
| V1      | Shared regular `def`           | Body visible   |
| V2      | Shared `def` across modules    | `@[expose]`    |
| V3      | Shared `def` across modules    | `@[no_expose]` |
| V4      | V3 + explicit interface lemmas | `@[no_expose]` |

Record:

- Target A kernel checking time.
- Target B kernel checking time.
- Additional wrapper/lemma kernel checking time.
- Combined kernel time across all affected declarations and modules.
- Peak memory.
- Compilation or kernel checking failures.
- Whether expensive unfolding is reduced.

Run benchmarks sequentially. Include the cost of compiling any new modules when evaluating overall performance, but report those costs separately from the consuming declarations.

## Deliverables

Provide a concise report containing:

1. The chosen wrapper location and exact Lean code.
2. Kernel timing comparison across V0–V4.
3. Whether `@[no_expose]` actually prevents the suspected expensive unfolding.
4. Any definitional equalities that stop working across the module boundary.
5. Whether explicit characterizing lemmas resolve those issues efficiently.
6. The smallest successful abstraction boundary, or the next higher-level boundary worth investigating.

**Success criterion:** Both problematic declarations pass ordinary kernel checking, without new axioms or `sorry`, and the combined kernel checking cost is substantially reduced.

**Priority:** Find a clean module-level abstraction boundary using wrappers and `@[no_expose]`. Avoid lower-level modifications and aggressive changes to kernel reducibility.
