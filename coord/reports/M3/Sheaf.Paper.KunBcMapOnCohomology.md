## What changed

Proved `AlgebraicGeometry.derivedBaseChangeMapPlus_cohomology_resolution` in
`Sheaf.Paper.KunBcMapOnCohomology`, without changing its signature or public imports.
The upstream `Etale.derivedBaseChangeMapPlus_fac_app` already supplies the bounded
resolution equation, so the arbitrary, potentially unbounded K-injective comparison
is unnecessary. A fully proved private helper `resolution_exchange_formula` performs
only the categorical naturality and inverse cancellation calculation. Applying
cohomology, with the existing source and single-functor comparisons, gives the first
conjunct. The upstream negative-vanishing theorem gives both terms of the second.
The helper assumes only invertibility of the source unit and localized comparison;
it assumes neither injectivity of pulled-back terms nor any new mathematical fact.

Updated the item's node proof, proof dependencies, proof origin and obsolete tool
approvals to match this shorter route. Both replacement and negative-vanishing nodes
already exist with proved upstream declarations. The replacement node's current
`blueprint_update` is precisely the bounded factorization used here. The unit has no
realized statement or steps that this route bypasses. No definitions, statements,
other modules, or public visibility changed; no change record is needed.

The final single-file server compile via `lcompile.py` passed without warnings in
39.3 seconds. Earlier proof attempts exceeded 60 seconds because their repeated
concrete derived-functor reductions were expensive in kernel type checking; the
private categorical calculation removes those repeated reductions. No timeout was
raised and no separate module was introduced.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.derivedBaseChangeMapPlus_cohomology_resolution`
(node `lem-kun-bc-map-on-cohomology`).

Original holes: 1. Closed: 1. Added: 0. Remaining: 0. Split off: 0.
The private helper is completely proved. This is a proof, not a decomposition.

## No longer needed

Removed every original proof-only import:

- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`:
  its injective-unit instance is already publicly available through the original
  derived-exchange import.
- `Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`: its general unbounded
  comparison, node `lem-weil-pbc-derived-exchange-termwise`, is replaced here by the
  proved bounded factorization `derivedBaseChangeMapPlus_fac_app`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`: no use of its
  `upperStar_abelian_exact` theorem is required; the exactness instances used by the
  statement already come from the retained public interface.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`, node
  `prop-weil-pbc-kinjective-resolutions-exist`: the representatives are quantified
  in the statement, so the proof does not choose resolutions.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`, node
  `def-weil-pbc-kinjective-resolutions`: no K-injective resolution predicate is used.

The proof also no longer directly cites
`lem-weil-pbc-dplus-injective-representative`: the existing proved negative-vanishing
lemma encapsulates that argument. It remains a transitive mathematical dependency
of that lemma. Removed obsolete tool approvals for the K-injective existence,
inverse-image exactness, arbitrary termwise comparison and injective representative
nodes. The exact-functor cohomology node remains for the stated canonical comparison.
These are local dependency removals; other library users may still need the modules.

## Where the brief, the DAG or earlier work was wrong

The planned arbitrary K-injective route was unnecessarily general for the actual
Lean signature, which quantifies bounded below homotopy-category representatives
with injective terms. The existing upstream bounded factorization and naturality
suffice. The original declaration docstring describes the more general resolution
argument; its signature is preserved exactly. The updated node records the precise
Lean proof instead. No mathematical statement error was found.

Searches: the required LeanFinder negative-cohomology query returned general derived
functor and injective-resolution lemmas. Loogle did not know the source-library
negative-vanishing identifier, and the msearch grep returned no hits. Direct source
search found and signature-checked both exact upstream results used in the proof.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
