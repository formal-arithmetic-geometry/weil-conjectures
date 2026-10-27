## What changed

Filled thirteen existing theorem proofs in `Sheaf.CategoryTheory.CondensedDerivedInvariants`.
Added a proved private helper showing that forgetting internal actions reflects isomorphisms.
Used this helper and the existing `forgetExact` theorem for exactness of trivial action,
group restriction and scalar restriction. Constructed the unique invariant restriction
from the normalized adjunction counits, and proved its normalization, signed shift
compatibility, derived additivity/shift existence, identity comparison and sheaf flat
resolutions from the existing APIs. All public signatures, definitions, attributes and
public imports are unchanged. A declaration-scoped unused-section-variable linter option
retains the existing three derived-category binders of `invariantRestrictionExist`.

## Proved and sorry left

Closed 13 of the original 23 holes; added 0 holes. This is a partial proof delivery,
not a decomposition. Names below are in `CategoryTheory.CondensedDerivedRestriction`.

Proved: `derivedProperties`, `groupMapNormalization`, `groupMapShift`, `identityActionExist`, `invariantRestrictionExist`, `restrictionAdditive`, `restrictionColimits`, `restrictionLimits`, `scalarExact`, `sheafFlatResolution`, `trivialAdditive`, `trivialColimits`, `trivialLimits`.

The 10 unchanged holes, all attached to `def-sfb-condensed-derived-invariants`:
- `actionAbelianData`
- `actionGrothendieck`
- `degreeZero`
- `forgetExact`
- `invariantsExist`
- `scalarActionExist`
- `scalarComparisonExist`
- `scalarComparisonShift`
- `scalarGroupExist`
- `scalarInvariantsExist`

## No longer needed

Removed these proof imports:

- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.DerivedAdjunctionShift`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`

Their particular ringed-topos composition, derived tensor, and adjunction-shift
specializations are not used by the proofs delivered here. The internal module
equivalence remains available through the public bar-data dependency. Canonical shift
compatibility uses the retained general `CanonicalRightDerivedAdjunctionShift` theorem.
The former node had no proof dependencies to prune. No module is withdrawn, and no
claim is made that the removed modules are globally unused or that the outstanding
scalar-comparison proofs will not need any of them.

## Where the brief, the DAG or earlier work was wrong

The item is attached to a definition node with an empty proof plan, despite its 23
auxiliary theorem holes. The delivery records the actual partial proof as node steps.
The apparent exact-forgetting declarations in `CondensedGroupAlgebraExactForgetful`
and the coherent action-space presentation only apply to profinite groups; they do
not close this file's arbitrary-topological-group existence holes. No compactness or
separation assumptions were added.

The current `literature/blueprint/latest` paragraph (3) gives the compactification
argument and no longer contains the older dense-lattice expansion named by this
node. This delivery preserves the reviewed statements and records their inherited
auxiliary-infrastructure source; it does not alter the unit route.

Validation: single-file remote compilation through `lcompile.py`; final delivery
also runs the required preflight and axiom probes.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
