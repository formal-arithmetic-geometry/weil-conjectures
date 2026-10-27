# Sheaf.CategoryTheory.ExactPostcompositionKInjectiveDescent proof scopes

## Reason

The stage-3 static preflight detects changed non-declaration commands when the private
proof helpers introduce new sections and section-variable blocks. This record documents
those proof scopes and the local elaboration/linter options. It does not authorize a
statement or definition change: all 13 existing public signatures, all four public
non-theorem bodies, and the three public imports remain verbatim. Nine theorem bodies
are proved, with zero remaining holes. The complete file compiles without warnings.

## Old

The existing module-level option, verbatim:

```lean
set_option autoImplicit false
```

The original public sections are `Unit`, `Descent`, `Composition`, `Identity`,
`Equivalence`, `Square`, `Transport`, and `CompositorTransport`. Their section-variable
blocks and the public declarations' signatures are unchanged.

## New

The module-level options, verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

The second option agrees with the existing package option in `lean/lakefile.toml` and
makes that elaboration setting explicit. New `Representatives` and `ExactSquare`
sections scope proved private helpers. Other proved private helpers live within the
existing sections. None supplies an instance, notation, or public declaration.

Two existing theorems, `exists_unique_normalizedKInjectiveDescent` and
`normalizedKInjectiveDescent_comp`, retain their hypotheses although the proofs do not
need the extra resolution hypothesis (or, for the first theorem, the adjunction).
Each has the following single-declaration wrapper:

```lean
set_option linter.unusedVariables false in
```

The two equivalence-compatibility theorems retain their existing section-instance
parameters, although their normalization-only proofs require fewer assumptions. Each
has the following single-declaration wrapper:

```lean
set_option linter.unusedSectionVars false in
```

These wrappers suppress unused-parameter warnings while preserving the original
interfaces. They introduce no mathematical assumption and do not affect importers.
The two extensionality theorems precede the existence/composition proofs that use them.
All four public non-theorem declarations retain their original bodies.

## Users

`tools/downstream.py` was run with all 13 public declaration names: there are zero
current Lean importers, and the only textual declaration uses it reports are within
the item module. Pending DAG parents remain relevant and the module is retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ExactPostcompositionKInjectiveDescent | C2 | Nine proofs and private proof scopes; public signatures and definitions unchanged. |

No consumer adaptation is required. The delivery changes no source-library module,
no public definition, and no target statement or its meaning.

## Status

landed 20261023T102512-L-2911624 2026-10-23 (merge of deliver/C2/Sheaf.CategoryTheory.ExactPostcompositionKInjectiveDescent)
