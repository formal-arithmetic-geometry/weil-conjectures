## What changed

Prove `WeilConjectures.IntegralSystemRealization.integralNativeDirectComparison` in
`Sheaf.SixFunctors.IntegralNativeDirectComparison`. The three existing comparison
definitions and the theorem signature stay verbatim unchanged.

Two new modules contain proved helpers in the namespace
`WeilConjectures.IntegralSystemRealization.NativeComparison`:

- `Sheaf.SixFunctors.IntegralNativeOrdinaryComparison`: the explicit
  `ordinaryPullIso`, `ordinaryEvaluation`, and `nativeFinitePullIso`, their adjunction normalization,
  `ordinary_pull_square`, and `transport_mates`.
- `Sheaf.SixFunctors.IntegralNativeDerivedComparison`: exact localization of that
  square (`derivedPullIso`, `derived_pull_square`) and preservation of finite adjoint conjugation
  (`finite_derived_conjugate`).

The main proof supplies the ordinary identity on sections, invokes the localized
square, then uses mate naturality and `DirectEvaluation.counit`. Its new imports are
proof-only. The helper modules use the existing native unit normalization and
exact-square factorization. Large sheaf constructions are kept behind their APIs;
the new finite comparison definition is irreducible, with a proved conjugation API.
After these transparency improvements the combined file still exceeded 60 seconds,
so the ordinary and derived arguments were separated into self-contained modules.
No existing shared interface or source-library file is changed.

Validation: `lcompile.py --all` compiled all three modules. The final source removes
the temporary profiling and tracing commands. The interface checker reports no
change to the existing item; its three original definitions are byte-for-byte
preserved. Final delivery runs the clean compile and preflight checks again.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralSystemRealization.integralNativeDirectComparison`
(node `lem-sf-integral-native-direct-comparison`). No holes added or split off;
no `sorry` remains in any delivered Lean file. Every helper theorem is proved.

The new proved public theorems are `NativeComparison.transport_mates`,
`NativeComparison.nativeFinitePullIso_conjugate`,
`NativeComparison.ordinary_pull_square`, `NativeComparison.derived_pull_square`,
and `NativeComparison.finite_derived_conjugate` in the namespace above.

## No longer needed

No original import, module or node is withdrawn. All original mathematical
prerequisites remain needed, directly or through the proved helper nodes.

The separate `integralDirectEvaluationMate_invertible` theorem and its extension
and K-flat machinery are unnecessary here: `ed` already supplies the evaluation
isomorphism. Only ordinary unit and whole-cochain normalization formulas are used;
there is no import of `Sheaf.SixFunctors.IntegralDirectEvaluationMateInvertible`.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The DAG's existing route is realized directly.
The counit equation determines the finite evaluation mate once the adjunctions
are fixed; the other `DirectEvaluation` fields and `Direct.factors` need not be
unfolded again. The proof compares whole-system morphisms before evaluation and
never assumes that finite evaluations are faithful.

The proved generic factorization helper from
`Sheaf.CategoryTheory.DerivedExactSquareComposition` is used as a tool for exact
localization, not as an alternative geometric route. Its private
`Functor.exactSquare_fac` is accessed by a proof-only `import all`.

## New nodes

`lem-sf-adjoint-mates-transport` records the generic mate transport calculation,
proved from the counit characterizations and naturality.

`lem-sf-integral-native-ordinary-comparison` records the ordinary inverse-image
square, its explicit coordinate isomorphisms, and the finite conjugation API.
It follows by transposing the normalized ordinary direct evaluation square.

`lem-sf-integral-native-exact-comparison` records exact localization of the
ordinary square and identification by the full cochain normalization. The explicit
`derivedPullIso` wrapper keeps its type stable without changing the original
`integralNativePullIso` construction.

`lem-sf-integral-native-finite-derived-conjugate` records the right-derived
finite coordinate comparison. Its proof uses the universal right-derived
factorization and the derived unit/counit factor equations.

All four nodes are proved in this delivery; none introduces a new obligation.
There are no change records because no other existing module or interface changed.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
