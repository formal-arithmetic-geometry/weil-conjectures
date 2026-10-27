## What changed

Filled the thirteen theorem proofs in
`lean/Sheaf/RingTheory/HenselianParameterRootDomainTower.lean`, preserving every existing
signature and definition. Added private proved helpers for quotient elimination, localized
quotients, local regularity, idempotents, and filtered colimits. Updated the existing node's
proof route and dependencies. The added elaboration option is recorded in
`coord/changes/henselian-parameter-root-domain-tower-elaboration.md`; the gate
requires that record for a module-level command change.

The proof reuses `ParameterRootAlgebra`, `ParameterRootColimit`,
`FilteredColimitIsDomain`, and `HenselianParameterRootRegularity`. At the general finite
stage, flat base change and the positive-power criterion replace the companion-coordinate
calculation. Radical containment and uniqueness of henselian idempotent lifting give
connectedness; connected regular affine schemes are integral.

## Proved and sorry left

Original holes: 13. All 13 are proved. `lcompile.py` compiled the module cleanly
in 35.9 seconds, with no warnings.
No holes added, no statements split off, and no `sorry` remains in the sandbox module.
The existing signatures, public imports, and definition bodies were compared with the
shared source and are unchanged. All lines have at most 100 characters.
The declarations are:

- `RingTheory.parameterRootRelations_vanish`
- `RingTheory.parameterRootMap_relation`
- `RingTheory.parameterRootMap_laws`
- `RingTheory.parameterRootDiagram_laws`
- `RingTheory.parameterRootCocone_naturality`
- `RingTheory.parameterRootPower_relation`
- `RingTheory.parameterRootFull_relation`
- `RingTheory.parameterRootFull_isColimit`
- `RingTheory.henselianParameterRoot_finite`
- `RingTheory.henselianParameterRoot_filtered`
- `RingTheory.henselianParameterRoot_local`
- `RingTheory.henselianParameterRoot_spectra`
- `RingTheory.henselianParameterRoot_degenerate`

All belong to `lem-sfb-henselian-parameter-root-domain-tower`.

## No longer needed

Removed proof imports `Mathlib.RingTheory.AdjoinRoot`,
`Mathlib.RingTheory.Localization.Submodule`, `Mathlib.RingTheory.Ideal.Maps`,
`Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.Algebra.Module.LocalizedModule.Exact`, and
`WeilConjectures.AlgebraicGeometry.Regular`. The root API supplies the monic basis,
the localized-module companion calculation is replaced by flat base change, and the
remaining removed imports duplicate declarations already publicly available through
retained imports.

Direct dependencies `lem-weil-pbc-monic-quotient-free` and
`lem-weil-pbc-localization-module-exact` are replaced by
`lem-sfb-simultaneous-root-algebra-api` and
`lem-weil-pbc-regular-sequence-powers`. The former may remain needed below the root API;
this delivery withdraws no module or declaration. All other planned mathematical
steps remain, with existing domain and root-colimit APIs used for their assembly.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned companion-coordinate proof is unnecessary:
the coefficient map is flat, and regularity is reflected through positive powers.
The full root quotient already has a proved universal property and directed-order
wrapper in `ParameterRootColimit`. The saved `.budget` start after launcher resume is 2026-10-23 16:35:19 UTC.
No worker changed budget metadata.
The first delivery preflight requested a change record for the elaboration option;
that record lists all consumers and explains the unchanged interfaces.
No definition, consumer, unit route, or target
statement changes.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
