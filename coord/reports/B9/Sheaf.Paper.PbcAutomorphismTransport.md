## What changed

Proved three of the seven remaining theorem holes in
`Sheaf.Paper.PbcAutomorphismTransport` without changing public statements,
definitions, public imports, or instance declarations. Retained the six proofs
from B2 already present in the starting snapshot.

- `pbcIsoModulePullback_isEquivalence`: lift the base-change site equivalence
  to module sheaves using the invertible adjoint coefficient map. The existing
  module adjunction then makes inverse image an equivalence.
- `pbcIsoIntegralPullback_linear`: use the existing constant-section equation
  to prove direct-image linearity, transfer it across the module adjunction,
  descend to the derived category, and restrict to the integral full subcategory.
- `pbcIsoScalarRightComparison_exists`: use the actual finite coefficient
  structure square and the inverse of `SheafOfModules.pushforwardCongr`.
  Its section maps are identities, which also proves uniqueness.

Added two proved private helpers for generic site/module equivalence and
normalized scalar restriction. Added proof-only imports of
`Sheaf.Paper.PbcScalarExtension` (including its private section equation),
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`, and
`Mathlib.CategoryTheory.Adjunction.FullyFaithful`.

The local irreducibility attributes prevent expensive unfolding of ordinary
pullback and derived localization constructions. They do not change their
bodies or the exported interface. See
`coord/changes/B9-automorphism-transport-proof-opacity.md`.
The DAG proof steps and dependency list now record the three additional proofs.
The full module compiled without warnings or errors through `lcompile.py` in
45.9 seconds (result `3be1c86b071858be64c2a9e1`).

## Proved and sorry left

Closed three original holes; added zero holes and zero split statements:

- `AlgebraicGeometry.Scheme.pbcIsoModulePullback_isEquivalence`
- `AlgebraicGeometry.Scheme.pbcIsoIntegralPullback_linear`
- `AlgebraicGeometry.Scheme.pbcIsoScalarRightComparison_exists`

Four original holes remain, all attached to
`def-wf-automorphism-completed-transport`, with their original source and proof
in their docstrings:

- `AlgebraicGeometry.Scheme.pbcIsoCompletedComparison_isIso`
- `AlgebraicGeometry.Scheme.pbcIsoAmbientPullback_preserves`
- `AlgebraicGeometry.Scheme.pbcIsoIntegralPullback_isEquivalence`
- `AlgebraicGeometry.Scheme.pbcIsoAmbientScalarComparison_exists`

The constructions cover arbitrary coefficient data and the zero ring: module
transport uses only an invertible ring map and a site equivalence. For the scalar
comparison, equal coefficient stages give the identity square and the same
identity-on-sections comparison. No extra finiteness or nonzero hypothesis is
introduced.

The delivery retains B2's proved coefficient-map invertibility, equality of
ordinary module pullbacks, normalized ordinary derived comparison, integral
scalar comparison, rationalization square, and rational scalar comparison.
No new definition, axiom, or hole inside a definition is introduced.

## No longer needed

No original import, node, or module is pruned. The remaining obligations still
need the original dependency route. No unit statement or realized proof step is
bypassed. The ordinary module equivalence uses Mathlib's generic site/module
construction instead of separately constructing inverse tensor transports.

The exploratory explicit import of
`WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` is unnecessary:
`PbcScalarExtension` already supplies that API through the proof-import context.
It is omitted from the final file.

## Where the brief, the DAG or earlier work was wrong

The original seven-obligation DAG paragraph was stale after these three proofs;
it now names the four remaining obligations. The coefficient and site
comparisons already available in the library suffice for the three closed
holes; no new mathematical statement is needed.

The naive concrete derived comparison expanded ordinary pullback and localization
constructions repeatedly and exceeded the per-file limit. An isolated prefix
compiled in 13 seconds after local irreducibility attributes were added.
No transparency checks were disabled and no file was split for delivery.

The existing DAG has a coarse dependency cycle through
`def-weil-pbc-finite-stage-pair-category` → `prop-weil-pbc-scalar-extension` →
`lem-per-quotient-completed-compositor-unit` →
`lem-sf-automorphism-completion-unit-comparison` → this node. This is already
present in the original dependency list. The new proofs use only the proved
coefficient-square and constant-section lemmas from scalar extension; they do
not use the downstream automorphism-completion theorem. The Lean import graph
is acyclic (`import_direction.py may` accepts the proof import). The DAG now
records the actual source node of those two lemmas; the pre-existing coarse
cycle is reported here for maintainer reconciliation.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
