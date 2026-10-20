# DerivedCategory.exists_unmarked_finiteFree_lift_of_nilpotent

## Reason

A complete proof uses Nakayama under the existing unit hypothesis, so it does not refer to
the original nilpotence hypothesis. The unchanged existential beta/theta binder names also
have no occurrences in the proposition body. Suppress only the unused-variable linter on
this declaration. This is proof elaboration context, not a mathematical interface change.

## Old

```lean
/-- The unmarked finite-free lifting data needed before checking the prescribed marking.
```

The theorem followed its existing docstring directly, with no local linter option.
Its body was `by sorry`. Public imports were StablyFreeComplexLift, Adjunction.Additive
and DerivedChangeOfRingsIndependentCoefficients, all preserved verbatim.

## New

```lean
set_option linter.unusedVariables false in
/-- The unmarked finite-free lifting data needed before checking the prescribed marking.
```

The same complete docstring and unchanged theorem signature follow this local option.

Its complete proof has no sorry. The option is scoped to this one declaration. The public
signature and all definitions and visibility remain unchanged. The proof imports now use
the existing private projective reduction comparison and finite-module Nakayama theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.UnmarkedFiniteFreeLift | G1 | Complete proof and local lint context. |
| Sheaf.RingTheory.NilpotentMarkedFreeComplexLift | unchanged | Same theorem signature and public imports; no adaptation. |

All transitive users receive exactly the same public interface. No target definition or
statement changes, and no consumer is adapted. The unused-variable linter option cannot
change any declaration's meaning or leak into an importing module.

## Status

landed 20261020T051307-L-1624416 2026-10-20 (merge of deliver/G1/Sheaf.RingTheory.UnmarkedFiniteFreeLift)
