## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.open_scalar_conjugate_normalization`
in `Sheaf.SixFunctors.OpenScalarConjugateNormalization`, with its statement and public
imports unchanged. The proof uses the existing internal K-flat mate normalization,
Mathlib's iterated inverse-mate identity, and the open unit mate equation. Taking
inverses of equal composite isomorphisms yields the required restriction equation.
Three proved private helpers handle ordinary open-unit invertibility and the two
formal categorical calculations; no public declaration was added.

The four auxiliary section-module derived categories are constructed from
Grothendieck abelianness transported across the fixed internal/section equivalences.
Local irreducibility keeps localization construction data folded; it exports no
attribute changes. The final file compiles without warnings under the default
heartbeat limit in 14.5 seconds through lcompile.py. No time limit was raised.
The DAG proof now records this shorter assembly and its actual dependencies.
Change record: `coord/changes/Q2-open-scalar-normalization-local-proof-context.md`.
Preflight conservatively requires this record for the local attribute command;
its downstream modules need no adaptation because the exported interface is identical.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.open_scalar_conjugate_normalization`
(node `lem-sfb-open-scalar-conjugate-normalization`).

Holes added: 0. Holes left in the delivered module: 0. Split off: 0.
The already stated dependency `AlgebraicGeometry.ProEtale.OpenInternalScalar.normalization`
(node `lem-sfb-open-internal-kflat-mate-normalization`) remains an existing dependency,
not a theorem added or modified by this delivery. This is a complete proof of the
assigned statement from the project's existing declarations.

## No longer needed

Removed direct proof imports `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
and `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`; the required interfaces
are already provided by `Sheaf.Paper.OpenInternalKFlatMateNormalization`.
Added that private proof import and the private proof imports
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful`.
All public imports are preserved.

The parent's proof no longer separately needs
`lem-sfb-open-coefficient-square-action-identification`
(`Sheaf.AlgebraicGeometry.OpenCoefficientSquareActionIdentification`), since the
existing internal normalization states the mate equation directly for the published
`derivedComapUpperStarIso.inv`. Its Lean declarations and attachment remain intact.
Removed the parent's obsolete direct tool approval `lem-sfb-alpha-iso`: coefficient
identification is encapsulated in the internal normalization dependency.
The unit route is unchanged; no module is withdrawn or claimed globally unused.

## Where the brief, the DAG or earlier work was wrong

The DAG's expanded composite-unit and scalar-transpose calculations are valid but
can be replaced by Mathlib's iterated inverse-mate and unit identities, already used
for the analogous fixed-scalar etale calculation in `Sheaf.SixFunctors.EtaleOpenTensor`.
The internal normalization signature requires four auxiliary small-Hom derived
category instances; these are constructed locally rather than added as hypotheses.
The initially imported modules did not export ordinary open full faithfulness or
the linearization full-faithfulness API; the final private imports provide them.
Identity opens, empty opens, zero objects and non-flat coefficient changes require
no separate cases: the categorical identities are unconditional and the existing
normalization applies to all unbounded objects without coefficient flatness.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
