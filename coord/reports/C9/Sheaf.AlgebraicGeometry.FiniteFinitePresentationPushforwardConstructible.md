## What changed

Proved `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_finite_finitePresentation`
in `Sheaf.AlgebraicGeometry.FiniteFinitePresentationPushforwardConstructible`, with its
existing signature unchanged. Three private, proved helpers transfer constructibility
under pullback and isomorphism and implement the affine finite-morphism case.

The affine proof uses the existing quasi-finite affine thickening decomposition, pulls
back twice, uses topological invariance for the module-valued adjunction unit, applies
finite etale pushforward constructibility, and descends through finite exchange.
The qcqs case uses Mathlib's `compactSpace_iff_exists` to choose an affine surjection,
then applies the affine case, finite exchange and surjective descent again.
The existing node's proof and dependencies now describe this route. A new Mathlib leaf
records the affine-surjection criterion; it adds no Lean declaration or proof obligation.

Validation: the entire edited module compiles with lcompile.py, without warnings.
The empty base/source case is covered by the zero-ring affine cover and the existing
thickening decomposition's empty finite etale case. No flatness is assumed anywhere.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_finite_finitePresentation`
(node `lem-weil-pbc-finite-fp-pushforward-constructible`).
Added 0 holes; split off 0 obligations. No sorry remains in the delivered Lean module.
The proof intentionally uses existing stated dependencies, including the still-open
finite etale pushforward, affine thickening decomposition, and surjective descent
results. This is a proof from those declarations, not a claim that the target's entire
transitive axiom closure is already sorry-free.

## No longer needed

Removed direct imports:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: no extension by zero
  is used in this direct-image argument.
- `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal`: replaced the
  affine-open locality step by an affine surjection, finite exchange and descent.
  Removed node `lem-weil-pbc-constructible-qcqs-affine-local` from this node's proof
  dependencies. It remains needed by the existing finite etale pushforward dependency;
  no claim is made that it leaves the whole target import closure.
- `Sheaf.AlgebraicGeometry.FiniteIsQuasiFinite`: a retired duplicate re-export. The proof
  uses `IsFinite.locallyQuasiFinite_and_quasiCompact` from the source library instead;
  its node `pqf-lem-finite-qf` remains used.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: no direct use of properness. The finite
  base-change and affineness facts are supplied by the retained imports.

All other declared proof dependencies remain needed. No module is withdrawn.
The unit's statement and its realized proof steps are untouched.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found wrong. The original affine-local criterion is
stronger bookkeeping than needed here: the already required surjective descent
result and finite exchange permit reduction along one affine surjection instead.
The old FiniteIsQuasiFinite module had already been retired; its useful source theorem
is retained and applied explicitly. No statement, definition, visibility or public
import changed, and no consumer adaptation or change record is needed.

## New nodes

`lem-weil-pbc-quasicompact-affine-surjection` records the existing Mathlib equivalence
`AlgebraicGeometry.compactSpace_iff_exists` as a Mathlib leaf. Its forward direction is
used once for the qcqs-to-affine reduction. It has no new module and no sorry. LeanSearch, semantic,
Loogle and source searches were recorded; blueprint and DAG searches found no duplicate.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
