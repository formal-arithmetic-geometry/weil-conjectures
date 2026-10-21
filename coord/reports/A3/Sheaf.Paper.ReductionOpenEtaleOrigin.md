## What changed

Restored the quarantined `Sheaf.Paper.ReductionOpenEtaleOrigin` module and proved
`AlgebraicGeometry.ProEtale.FiniteReductionOrigin.reduction_open_etale_origin`.
Two proved private helpers assemble bounded constructible etale descent and compute
finite reduction using a flat complex supported in the Tor interval. Exact faithful
comparison reflects the bounds, exact open extension preserves them, and the canonical
comparison maps supply the pinned `FixedEtaleOriginWitness` values.

The archived scalar-extension occurrences needed explicit universe and canonical
`EssentiallySmall` arguments to elaborate. Their functors and mathematical types are
unchanged. The change record is
`coord/changes/A3-reduction-open-etale-origin-universes.md`.
The item node records the shorter proof route and retains its Lean attachment and parent
mathematical role. No upstream module, target statement, or unit route is changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.FiniteReductionOrigin.reduction_open_etale_origin`
(node `lem-fix-reduction-open-etale-origin`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivery. The private helpers `scalar_bound` and
`bounded_origin` have complete proofs.

## No longer needed

Removed imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.RingedCoefficientPullbackComparison`
- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

The intrinsic constructibility conversion uses finite fixed-module models directly,
then existing fixed-module bounded constructible descent. The finite reduction bound
uses the bounded flat model and the chosen-adjoint K-flat representative theorem;
it needs no ringed coefficient realization or comparison of derived tensor products.
The pro-etale extension exactness and open comparison already exist in the source
library, and the canonical etale open scalar comparison supplies the required route.

Removed direct proof dependencies:

- `lem-sf-proetale-constructible-origin`
- `lem-pur-coefficient-pullback-comparison`
- `def-weil-pbc-site-comparison-morphism`
- `prop-weil-pbc-site-comparison-finite-level`
- `lem-pur-derived-change-of-rings`
- `lem-pc-kflat-resolution`
- `lem-pur-change-of-rings-tensor-comparison`
- `def-weil-derived-tensor`
- `def-weil-finite-tor-amplitude`
- `def-kun-derived-tensor`
- `lem-cbc-proetale-extension-zero`
- `lem-fix-open-scalar-tensor-normalization`

Also removed the obsolete top-level `tool_uses` approvals for the removed dependencies;
remaining approvals stay in their original order. These are local dependency removals,
not claims that the modules have no other target consumers. No module is withdrawn or
deleted, and no upstream declaration or proof is removed.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, rather than withdrawn. Its archived scalar comparison
definitions hit unresolved universe constraints on canonical small-site instances;
explicit existing universe arguments repair elaboration. `tools/downstream.py` reports
zero live Lean consumers; searches of quarantined modules find only this item. Its DAG
parent `lem-fix-compact-support-coefficient-change` still needs the statement.

The old plan is mathematically sufficient but its ringed scalar and generic K-flat
resolution detour is unnecessary: a bounded flat representative preserves the exact
interval under ordinary extension of scalars. This works for every ring map, including
nonflat reduction, and retains all canonical witness clauses. The etale bounded origin
is supplied by the existing proved source theorem rather than the ringed-origin wrapper.
Edge cases include identity/empty open immersions, equal coefficient levels and the
zero complex; the argument uses no positive-dimensional or nonzero-object hypothesis.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
