## What changed

Proved `WeilConjectures.SystemProjectionFormula.projection_natural` in
`Sheaf.Paper.SystemProjectionFormulaCoherence` from naturality of the three
transformations in its defining word. A proved private helper establishes the
same equation on all systems. The existing public signature, geometric parameters,
definitions, public imports and remaining theorem statements are unchanged.
The unused-section-variable linter is disabled only for the existing public
naturality theorem because its retained geometric parameters are unnecessary for
this direct proof. Updated its docstring and the node proof to explain this route.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.SystemProjectionFormula.projection_natural`.
Added zero holes and zero split statements.

The two remaining holes are unchanged, both attached to
`lem-pur-system-level-projection-formula-coherence`:

- `WeilConjectures.SystemProjectionFormula.projection_evaluation`.
- `WeilConjectures.SystemProjectionFormula.system_projection_formula_coherence`.

The naturality argument is independent of any sorry theorem: it uses only
naturality of properProjection after uncurrying, the open projection comparison,
and the inverse pullback compositor with the compactification equality cast.
Remote single-file compilation is the validation for this packet.

## No longer needed

Removed these ten unused private proof imports from the item:

- `Sheaf.CategoryTheory.SystemRingedSequenceSite`.
- `Sheaf.Paper.RingedProjectionTensorComposition`.
- `Sheaf.Paper.SystemCompactificationProjectionSubstitution`.
- `Sheaf.Paper.SystemNormalizedTensorClosure`.
- `Sheaf.SixFunctors.CompositionProjectionMate`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.PullbackTorAmplitude`.
- `Sheaf.Paper.FiniteCoefficientTensorCtf`.
- `Sheaf.Paper.OpenExtensionFiniteTor`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`.

Their associated nodes are not needed for the proved naturality clause. The
remaining two holes still have the original proof plan, so their proof_deps and
tool_uses are retained: this packet does not assert that those modules or nodes
are globally unnecessary, and withdraws none. All public imports remain.

## Where the brief, the DAG or earlier work was wrong

The earlier naturality sketch routed through a ringed sequence site and ringed
projection coherence. The specified projection already consists of natural
transformations, so their naturality squares suffice directly. No domain closure,
finite-level conservativity, geometric finiteness, or comparison with ringed-site
models is required for this clause. No statement or definition was found false.
The actual finite normalization and composition transport still need separate
proof work; this delivery makes no claim to have proved them.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
