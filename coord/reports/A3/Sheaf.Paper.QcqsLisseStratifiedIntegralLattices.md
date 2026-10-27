## What changed

Proved `AlgebraicGeometry.ProEtale.qcqs_lisse_stratified_integral_lattices` in
`Sheaf.Paper.QcqsLisseStratifiedIntegralLattices`, with its signature unchanged.
Private proved helpers identify the two local-freeness predicates, select a finite affine
etale cover using compactness for an arbitrary neighbourhood property, assemble its lattices,
construct the finite-field stratified lattices, and identify the adjunction comparison with
`Mod.extendHom`. Generic coefficient predicates, base-change lattice descent, and diagram
pack/unpack helpers keep kernel conversion from expanding the sheaf pullback constructions.
The image-rationalization helper uses exact scalar extension, the localization counit,
and the ordinary pushforward comparison in the given normed-field structure.
The algebraic-closure assertion then follows from the existing finite coefficient model;
all four factors of its specified final composite are isomorphisms.

The proof uses the existing affine etale lattice and finite-coproduct lattice constructions,
Stacks 03S0 stratification, locally free pullback, and finite etale trace-image descent.
It reuses the proved generic assembly helper through `import all`;
the trace-image rationalization is proved from the three existing localization APIs.
Only this item module, its proof-route node and the local-context change record are changed.
All public imports and four original protected unit-route imports are retained.
Change record: `coord/changes/A3-qcqs-lisse-stratified-lattice-proof-context.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.qcqs_lisse_stratified_integral_lattices`
(node `lem-sfb-qcqs-lisse-stratified-integral-lattices`).
No holes added or split off. No `sorry` remains in the delivered Lean module.
The proof uses previously stated dependency theorems, including
`AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleTrace_lattice`,
whose existing hole is outside this delivery.

## No longer needed

Removed these direct proof imports and their direct dependencies from this item's route:

- `Sheaf.Paper.StratifiedLatticeRank` (`det-lem-stratified-lattice-rank`): the affine
  lattice theorem already permits varying ranks.
- `Sheaf.Paper.StratifiedLatticeScheme` (`det-lem-stratified-lattice-scheme`): reuse
  the existing affine etale lattice theorem instead of constructing a representing scheme.
- `Mathlib.AlgebraicGeometry.Sites.Etale` and
  `WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit`
  (`def-weil-pbc-etale-site`, `lem-weil-pbc-etale-covering-sieve-finite-affine-refinement`):
  select finitely many of the already affine point-neighbourhoods by compactness.
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry`
  (`lem-weil-pbc-proetale-qcqs-finite-family-geometry`): reuse the finite-affine
  coproduct geometry helper, which proves the assembled source affine and qcqs directly.
- `Sheaf.AlgebraicGeometry.InternalExtensionInverseImage`
  (`lem-sfb-internal-extension-inverse-image`): use the existing `CondensedRing.pullIso`
  construction in `ChangeOfCoefficients` directly; its adjunction-based definition does not
  depend on this separate theorem.
- `lem-sfb-embedded-lattice-coefficient-comparison`: the affine etale lattice theorem
  already supplies internal modules over the continuous coefficient rings, so no separate
  conversion from topological embedded lattices is needed here.
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit`
  (`lem-weil-pbc-finite-etale-etale-local-split`): the existing finite-etale trace-lattice
  theorem encapsulates this local geometry; it may remain a transitive dependency.

The original imports `Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage`,
`Sheaf.Paper.CartesianCoefficients`, `Sheaf.Paper.ContinuousLatticeSum`, and
`Sheaf.Paper.LatticeSheafLocallyConstant` are retained because preflight identifies
them as unit-route modules. Their top-level tool approvals are retained in original
order. These four modules are not claimed as pruned. No global withdrawal is claimed.

Unused top-level `tool_uses` approvals are removed in their original order. The newly
used affine-etale, finite-coproduct, continuous finite-etale trace and coefficient localization
nodes are existing tools implementing this same lattice argument. The four protected
unit-route modules remain imported. No unit statement or realization is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous route repeated the rank/lattice-scheme construction even though the
library already supplies affine etale lattices with varying rank and their coproduct
assembly. The published etale-local lattice theorem assumes a Noetherian base;
its proof only uses that assumption to extract a finite subcover. The private helper
here instead applies compactness directly, so the original qcqs statement is retained.
The direct dependent-choice proof of the compact cover caused excessive kernel reduction.
Keeping the neighbourhood property abstract in a generic compact-cover helper avoids that
expansion. The existing private trace-image lattice helper asks for a nontrivially normed
field, but each of its localization ingredients works with the given normed field.
The private helper here proves the same image argument directly from those ingredients,
avoiding a costly change of normed-field instances. The normed-field result is transported
to the finite-subfield coefficient diagram by
an explicit proved equality; generic packing and unpacking avoids expanding the scalar
extension and sheaf pullback while comparing these interfaces. The complete file compiled
without warnings in 30.4 seconds before the delivery check. No existing definition,
target statement, or adopted source-library declaration is changed.

Preflight required a change record for the local reducibility and image-instance
priority attributes. The record documents their scope and the unchanged public API.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
