# Lean 4 Kernel Performance — Top-Down Investigation

## Goal

We have confirmed that kernel type checking dominates runtime (~400 s), with two particularly expensive declarations:

- `leftDerivedUpperStarTensorComparison_app_app_comp` (~167 s)
- `leftDerivedUpperStarOplaxMonoidal` (~206 s)

Although kernel diagnostics show extensive unfolding of `Preadditive` and hom-group structures, **do not investigate or modify those lower-level definitions yet**. They may simply be consequences of expensive computations triggered at a higher level.

The goal is to **work top-down from these two declarations**, identify the smallest expensive subterms or type conversions, and determine where an abstraction boundary could reduce kernel checking costs.

## Experiment 1: Declaration-Level Isolation

Start with the two expensive declarations.

For each declaration independently:

1. Record its original kernel checking time.
2. Temporarily replace its entire body with `sorry`, preserving the declaration's type.
3. Re-run with kernel checking enabled and `Elab.async=false`.
4. Record the change in total runtime, peak memory, and per-declaration kernel time.

Be careful: replacing the body of a `def` can also change kernel reduction in downstream declarations. Record those effects separately.

**Goal:** Confirm the contribution of each declaration and identify whether expensive checking is localized or propagated into subsequent declarations.

## Experiment 2: Top-Down Subterm Bisection

Restore the original definitions. Investigate the internal structure of each expensive declaration.

### Target A: `leftDerivedUpperStarTensorComparison_app_app_comp`

Start with the highest-level proof components:

- `e₁`
- `e₂`
- `e₃`
- The final proof involving `exact h`

Replace one component at a time with a typed `sorry`, leaving all other components unchanged.

If replacing one component significantly reduces kernel checking time, recursively inspect that component's immediate subterms.

If replacing individual components has little effect, test combinations to detect repeated or shared costs.

### Target B: `leftDerivedUpperStarOplaxMonoidal`

Start at its outermost construction.

1. Identify the major arguments or fields, especially those supplied to `ofLaxSquare`.
2. Replace one argument or field at a time with a typed `sorry`.
3. Measure the kernel checking time after each replacement.
4. Recursively inspect only the expensive branches.

Do not descend into category instances, hom groups, or `Preadditive` internals unless the experiments specifically lead there.

### Important Distinction

Try to distinguish:

- **Expensive term checking:** The kernel spends time checking a constructed subterm.
- **Expensive type conversion:** The kernel spends time establishing definitional equality between the subterm's type and its expected type.

For example, if replacing `exact h` with `sorry` removes most of the cost, investigate the conversion between the inferred type of `h` and the expected goal, rather than assuming that constructing `h` is expensive.

**Goal:** Identify the smallest high-level expression or type conversion responsible for the slowdown.

## Experiment 3: Test an Abstraction Boundary

Once an expensive subterm has been identified, try extracting it into a separate declaration.

For proof-valued subterms, prefer a named auxiliary theorem:

```lean
private theorem auxiliaryLemma (...) : P := by
  -- Original proof
  ...

-- In the original declaration:
exact auxiliaryLemma ...
```

For data-valued subterms, consider a separate definition, but remember that ordinary `def` bodies remain reducible to the kernel.

Measure:

- Kernel time for the extracted declaration.
- Kernel time for the original declaration after extraction.
- Combined kernel time and peak memory.
- Whether downstream declarations become faster or slower.

If the cost is merely transferred to the auxiliary declaration, the extraction has not solved the problem.

Do not introduce `opaque` or `irreducible_def` yet unless the preceding experiments identify a specific expensive reduction boundary that warrants testing.

## Benchmark Rules

- Use `Elab.async=false` and `debug.skipKernelTC=false`.
- Keep the original proof logic unchanged except for temporary diagnostic substitutions.
- Run expensive variants once initially; repeat promising results.
- Record per-declaration kernel timing whenever available, not just total file runtime.
- Use `sorry` only for diagnosis. The final solution must pass normal kernel checking without `sorry`.

## Deliverables

Produce a concise Markdown report containing:

1. Declaration-level isolation results.
2. A table of subterm replacements and corresponding kernel times.
3. The smallest identified expensive subterm(s) or type conversion(s), including relevant Lean code.
4. Results of any abstraction-boundary experiments.
5. A recommended next step, focusing on the **highest-level location where expensive kernel checking can be avoided**.

**Priority:** Locate the expensive operation by progressively descending from the two problematic declarations. Avoid speculative changes to shared lower-level Mathlib infrastructure.