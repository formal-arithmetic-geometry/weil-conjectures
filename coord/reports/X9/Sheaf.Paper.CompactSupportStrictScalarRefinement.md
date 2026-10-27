## What changed

Updated the two terminal proof steps of `supportRefinementIso_coherence` to use explicit
`simpa only` normalization (`Iso.refl_inv` and the unchanged composition expression).
All imports, declarations, and theorem statements are unchanged. The six existing
`sorry` declarations remain in the module.

## Proved and sorry left

No previously holed declaration was closed. The following six existing declarations
still contain their original `sorry` proofs:

- `WeilConjectures.PurStrictScalar.scalar_clopen_projection`
- `WeilConjectures.PurStrictScalar.scalar_properOpen_alpha`
- `WeilConjectures.PurStrictScalar.scalar_compactification_composition`
- `WeilConjectures.PurStrictScalar.scalar_refinement_origins`
- `WeilConjectures.PurStrictScalar.scalar_refinement_origins_E` (new split node)
- `WeilConjectures.PurStrictScalar.scalar_refinement_origins_F` (new split node)
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinement`
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinementCoherence`

The edited `supportRefinementIso_coherence` proof compiles and remains fully proved.

## No longer needed

None. Every recorded import and dependency remains part of the module's current
proof or public declarations.

## Where the brief, the DAG or earlier work was wrong

The direct specialization of `scalar_properOpen_gamma` reaches only the central
proper/open mate equation. The target `scalar_compactification_composition` additionally
contains `compositionD` and `comparison` compositors, and the current imported API has
no theorem identifying those scalar mates with the required compositor pasting. No
statement or dependency was changed.

## New nodes

The origin conjunction was decomposed into two strictly smaller statements, each with
one coefficient family and no unused compactification or opposite calculus argument:

- `lem-pur-compact-support-strict-scalar-refinement-origins-e`, proved as the E-side
  `scalar_refinement_origins_E` declaration in `Sheaf.Paper.ScalarRefinementOriginsE`.
- `lem-pur-compact-support-strict-scalar-refinement-origins-f`, proved as the F-side
  `scalar_refinement_origins_F` declaration in `Sheaf.Paper.ScalarRefinementOriginsF`.

Their proofs remain `sorry`; the parent origin conjunction is proved by pairing these
independent statements.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
