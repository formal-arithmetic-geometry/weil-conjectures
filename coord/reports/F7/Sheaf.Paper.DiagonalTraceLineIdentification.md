## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceLineIdentification`
by inverting the normalized ordinary scalar-extension adjunction unit. Reused the proved
private coefficient-map isomorphism and additive transport helpers from
`Sheaf.Paper.DiagonalTraceCoefficientIdentification` through a proof-only `import all`.
The comparison of the two underlying additive towers is constructed from their recorded
section, restriction, and transition equations. Its normalization follows from the
ordinary unit-section equation and the forgetful functor's morphism equation.

The public statement, definitions, and public imports are unchanged. Updated the item's
node proof to describe the actual ordinary-adjunction argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceLineIdentification`
(node `lem-sfb-diagonal-trace-line-identification`). No holes added or split off.
No `sorry` remains in the delivery.

Validation: the remote compiler accepted the complete item with no diagnostics in
34.1 seconds. The declaration statement is unchanged, and every line is at most
100 characters.

## No longer needed

The proof does not use `lem-coef-semilinear-derived-sections` or its theorem
`WeilConjectures.SemilinearSections.semilinearDerivedSections`: ordinary restriction
along a ring isomorphism and the already recorded ordinary adjunction suffice.
Removed that planned proof dependency from the item's node. No existing import was
removed; no module is withdrawn. The semilinear system-model definitions remain used.

No completed root-limit cone, derived trace, normalized Chern hypothesis, or freeness
of the root module is needed. The coefficient-identification module remains needed
for its proved finite coefficient-map helper.

## Where the brief, the DAG or earlier work was wrong

The earlier route described the required tensor unitor but did not realize it in Lean.
The ordinary adjunction unit provides the same normalized comparison, with invertibility
following from restriction being an equivalence. No statement correction is required.
The rework row was checked before copying: the item source is currently restored under
`lean/Sheaf/Paper/DiagonalTraceLineIdentification.lean`; this delivery preserves its
attachment and does not withdraw any quarantined source.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
