## What changed

Proved `WeilConjectures.PurityFiniteSetting.diagonalEtaleAlphaSquare` without changing
its statement, definitions, or public imports. Added proof-only imports of
`DiagonalExchangeNaturality`, `ComparisonPullbackDerivedCoherence`,
`SectionExceptionalFibreCoherence`, and `DiagonalEtaleSourceEndpoint`.

The ordinary argument uses the Cartesian intermediate product Q, the existing
right-mate locality/base-change equation, dualizing exchange pasting, and restriction
of inverse exchanges along sections. Proved private coherence helpers identify this
with the published `sourceOrdinary`. The existing counit characterization identifies
structural locality with the specified normalized tensor mate. Pullback-comparison
naturality transports the one-sided equation to the pro-etale site; the two equations
are combined through the common source diagonal.

Updated the item's node proof and proof dependencies to record these actual helpers.
The final module passed `lcompile.py` with exit code 0 in 27.3 seconds, with no
errors or warnings. The original theorem signature and public imports were checked
against the shared source and are unchanged.

All implementation changes are confined to the item module. No shared interface,
source-library declaration, or unit route changes.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.PurityFiniteSetting.diagonalEtaleAlphaSquare`
(node `lem-pur-diagonal-etale-alpha-square`).

No holes added, no statements split off, and no `sorry` remains in the delivered
module. The private helper definitions contain actual constructions, and every
private helper theorem is proved.

## No longer needed

No original Lean imports removed and no modules withdrawn or globally pruned.
The node no longer cites `lem-amb-etale-left-comparison-base-change` directly:
its right-adjoint form and pasting law are already proved helpers of
`lem-trf-section-exceptional-fibre-coherence`, which replaces that direct dependency.
The left-comparison theorem remains used transitively; its mathematics is not
claimed to have been pruned. All other original dependencies remain used.

No DNC-invariance, vector-purity, normal-bundle, target-open-rho, or coefficient-unit
compatibility theorem is used by this proof. The original public imports remain
because they supply the statement's specified source and dualizing transports.

## Where the brief, the DAG or earlier work was wrong

The existing plan is valid. Its right-mate interchange and section-coherence steps
already have proved library helpers, accessible with proof-only `import all`.
Consequently the alpha square needs no further split despite the earlier chain
of decompositions. The proof includes the identity transports of the two composite
maps to the common source, and adds no nonempty-scheme or positive-rank assumption.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
