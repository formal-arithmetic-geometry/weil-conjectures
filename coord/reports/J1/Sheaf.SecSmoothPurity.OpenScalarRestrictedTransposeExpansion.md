## What changed

Completed `AlgebraicGeometry.ProEtale.openScalarRestrictedTransposeExpansion` with
its signature unchanged, preserving the definition of `openScalarRestrictedTranspose`.
The first conjunct follows by transposing the proved canonical `openScalarIso_unit`
identity. Private proved category-theory helpers derive this counit equation, expand
the inverse adjunct, and substitute the two factor equations. The last two conjuncts
use inverse-Hom naturality, functoriality, and the hypothesis `hr`.

A proof-only `import all Sheaf.SecSmoothPurity.OpenScalarExchange` accesses the existing
proved private unit identity. Updated the existing node's proof route and dependency
list. Local irreducibility/transparency controls prevent unnecessary unfolding of
large normalized adjunctions and comparisons.

Change record: `coord/changes/j1-open-restricted-transpose-proof.md`.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.ProEtale.openScalarRestrictedTransposeExpansion`
(node `lem-sp-open-scalar-restricted-transpose-expansion`).

Server single-file validation: compiled in 57.1 seconds; added the requested explanatory
comment for the declaration-local heartbeat budget before final delivery validation.

Added zero holes. No sorry remains in the delivered module. All private helpers are
proved. This is a proof, not a decomposition; no new statement modules or nodes.

## No longer needed

The proof does not need `lem-sp-open-proetale-counit-scalar` or
`Sheaf.Paper.OpenProEtaleCounitScalar`: the specified normalized open scalar map
already has a proved unit transpose, and the counit identity follows formally.
The node's proof dependency on that theorem is removed. The composite-adjunction
node remains: the existing definition of the transpose uses its composition
coordinates, and the proof expands those inverse Hom equivalences directly.

Removed these redundant public imports (the retained definition interface and
normalized-tower module supply the declarations used in the statement):

- `Sheaf.SecSmoothPurity.ReductionDirectImage`
- `Sheaf.SecSmoothPurity.DirectImageScalarOperations`
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`
- `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`
- `Sheaf.Paper.MateOpenRestriction`
- `WeilConjectures.Compactification.RefinementCategory`

`Sheaf.SecSmoothPurity.ReductionDirectImageComparison` is now imported directly as
the definition interface; its theorem dependencies remain available transitively.
No claim is made that any of these removed direct imports is globally unreachable.

No module is withdrawn. An unfinished parent can still need this item despite the
absence of current Lean importers. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original DAG proposed transporting the finite-Tor site-level scalar-counit
identity. In the stipulated normalized ringed coordinates this extra transport is
unnecessary: `openScalarIso_unit` already supplies the exact canonical normalization,
and `directImageScalarPullbackIso` equals `tensorPullbackIso` definitionally. The
actual open counit, the arbitrary morphism r, and all public hypotheses/conclusions
are preserved.

Checked the identity open, empty open, zero object, zero morphism, identity scalar
map, and nonflat coefficient-map cases: the argument uses only naturality and
triangle identities and imposes no new invertibility or flatness requirement.
The blueprint unit route stays unchanged. The rework row is a quarantine/build
record; the current item source is present, copied unchanged before proving it.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
