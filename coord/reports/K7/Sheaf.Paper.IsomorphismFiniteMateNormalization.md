## What changed

Proved `WeilConjectures.PurityFiniteSetting.isomorphismFiniteMateNormalization` in
`Sheaf.Paper.IsomorphismFiniteMateNormalization`. The theorem statement and the
three existing definitions are unchanged. Private proved helpers transport mates
through the intrinsic equivalences and direct-image coordinates, pass the proper
comparison through right derivation, and identify the ordinary and derived open
reindexing by iterated mates and the open-unit equation. The final compactification
and section clauses follow by evaluating their definitions.

The proof imports the existing proved private calculus of
`ProEtaleOpenSquareExchange`, `FixSiteOpenExchangeSheaf`,
`EtaleOriginOpenRestrictionTransport`, and `UnboundedAbelianExchangeComparison`.
The node's proof, proof dependencies, and proof origin now describe this argument.
No source-library module, public signature, public import, or definition changed.
The exact module compiled in 20.5 seconds after removal of development options.
Two unused simp arguments from that run were removed before delivery. Local irreducibility
attributes and generic categorical helpers avoid unfolding the realization and
localized-adjunction constructions in concrete proofs.

## Proved and sorry left

Closed the one hole in
`WeilConjectures.PurityFiniteSetting.isomorphismFiniteMateNormalization`.
The item's hole count is 1 before and 0 after. No holes were added or split off;
every new private helper is proved. There are no remaining `sorry` declarations
in this delivery.

## No longer needed

Removed private imports:

- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.SixFunctors.OpenTensorNormalization`

The proof no longer uses the originally planned results
`lem-weil-proetale-isomorphism-inverse-image`, `def-weil-open-immersion`,
`lem-weil-pbc-proetale-derived-pullback-composition`,
`def-weil-presheaf-modules-sheafification`, `lem-cbc-proetale-extension-zero`, or
`lem-sf-open-tensor-normalization` as proof steps. The ordinary reindexing was
already constructed in the item's definitions; existing transport calculus
normalizes it without repeating presheaf reindexing or tensor arguments.
The corresponding obsolete `lem-sf-open-tensor-normalization` tool-use entry
was removed. The Cartesian-open module remains publicly imported because its
canonical derived adjunction occurs in the statement; its main restriction
theorem is not invoked. The intrinsic extension-by-zero and inverse-image
constructions remain necessary definitions, including dependencies already
reached through public imports. No module is withdrawn, and no assertion is made
that other consumers no longer need the listed modules or results.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The recorded six-step plan
was longer than necessary given the existing proved generic transport and
localization calculus. The new route proves the identical six-clause statement
and retains the package unit's route; its realized record assigns this auxiliary
node no separate unit-level statement or proof step. Identity morphisms, an empty
open, and an identity open require no additional cases because the argument uses
unrestricted adjunction identities and the supplied Cartesian squares.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
