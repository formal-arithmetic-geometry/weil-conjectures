## What changed

Proved both theorems of `Sheaf.Paper.ClosedScalarDomains`, preserving all existing
signatures, definitions, public imports and docstrings. Added two proved private
helpers: `closedScalar_fixed_domain` converts fixed-scalar bounded constructibility
and an ordered Tor interval to the recorded intrinsic domain and an etale origin;
`closedScalar_exceptional_domain` applies the published preservation theorem once.

The scalar proof descends via the already proved `intrinsic_bc_realization_iff`
and `etale_bc_iff` helpers, imported privately with `import all` from
`Sheaf.Paper.FiniteCompactSupportConstructibility`. These helpers use the finite-ring
constructible-origin theorem, not the compact-support theorem. It uses the existing
etale scalar flat-model theorem and the canonical `pbcComparisonReduction` scalar
mate. The exceptional proof applies preservation separately over E and L using the
supplied chart family, and applies scalar preservation on X and Z.

Updated the item's node proof, proof dependencies and proof origin to describe the
actual argument. No other Lean module or consumer is changed. No new definition,
public declaration, axiom, or split-off statement is introduced.

## Proved and sorry left

Original holes: 2. Closed: 2.

- `WeilConjectures.closedScalarDomains_scalar`.
- `WeilConjectures.closedScalarDomains_exceptional`.

Holes added: 0. Sorries remaining in the delivered module: 0. This is a proof,
not a decomposition. Both private helpers are completely proved.

## No longer needed

Removed the private direct imports `Sheaf.Paper.ProEtaleConstructibleOrigin` and
`Sheaf.AlgebraicGeometry.ComparisonTorInterval`. Their wrappers are unnecessary:
the proved finite-ring intrinsic-constructibility bridge and intrinsic Tor transport,
together with the source-library Tor comparison, provide the needed interfaces.

The proof does not use the declared dependency
`lem-sp-etale-chart-comparison-isos` / `Sheaf.AlgebraicGeometry.EtaleChartComparisonIsos`.
The canonical, already proved `pbcComparisonReduction` supplies its required scalar
clause directly, without constructing any chart, twist, or annihilator data. That
module was never imported into this item.

Removed the obsolete direct proof dependencies and corresponding old tool-use
entries `lem-sf-proetale-constructible-origin`, `lem-exc-comparison-tor-interval`, and
`lem-sp-etale-chart-comparison-isos`. Their mathematical roles are covered by the
explicit replacement dependencies in the node. No declaration or module is withdrawn;
no assertion that these modules have no other consumers is made. All public imports
are retained as the existing exported interface.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was necessary. The original plan unnecessarily
used the large chart-comparison theorem for a scalar comparison already proved in
`WitnessCompatibility`. The intrinsic and fixed-scalar finite-Tor predicates are
not definitionally equal, as the preservation node's own note warns; the proof
explicitly transports both bounded constructibility and Tor amplitude. The resulting
ordered interval is proved using nonnegativity of the chart maximum and dimension.
The bundled Over structure maps also require explicit local property instances for
the preservation theorem's typeclass interface.

Checked the argument at nonflat coefficient maps, equal interval endpoints, identity
maps, and empty schemes/charts. No step assumes coefficient-map flatness, a nonempty
scheme, or a nonempty chart family. The unit's preservation route remains in place.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
