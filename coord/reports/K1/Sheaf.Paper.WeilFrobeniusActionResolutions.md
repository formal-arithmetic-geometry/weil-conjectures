## What changed

The item proof constructs the ordinary Frobenius realization on the existing `AsSmall`
pro-etale site, then proves every field of `ResolutionAssertions`. Postcomposition keeps
object domains and covering arrows unchanged. The coefficient isomorphism comes from
continuous/cocontinuous restriction commuting with abelian sheafification, lifted through
its monoid adjunction and the existing reconstruction of section rings. Its normalization
is checked on the original finite-subextension-valued generators.

Derived conservativity follows from the natural cohomology comparison and conservative
ordinary forgetting. Constructibility transports along that comparison. Flat resolutions
come from the action-site module category and its additive equivalence. K-flatness and
flat terms are preserved using the supplied ringed-topos pullback theorem and uniqueness
of left adjoints. The exact orbit-induction adjunction gives preservation of K-injectives.
Grothendieck abelianness of fixed pairs supplies the functorial injective replacement.

## Proved and sorry left

The complete proof replaces the sole original hole,
`WeilConjectures.WeilFrobeniusAction.frobenius_action_resolutions`
(node `lem-sf-weil-frobenius-action-resolutions`). There are zero `sorry` occurrences
in the item and zero new holes, public statements, or split-off modules. Validation
of the complete module is pending; the generic normalized coefficient-ring
construction already compiled independently as a diagnostic prefix of this file.
The existing definitions, theorem signature, and public imports are unchanged.

## No longer needed

Removed proof imports:

- `WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites`: continuity and the
  restriction equivalence are proved directly from the concrete site model.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: use the generic
  functorial K-injective replacement directly on the Grothendieck category of fixed pairs.

The node `lem-weil-pbc-site-equivalence-is-morphism-of-sites` is not used by this proof.
The node `prop-pur-kinjective-resolutions-exist` is also not used directly; generic
functorial replacement is applied to fixed pairs. The two corresponding obsolete
`tool_uses` entries are removed from the item node. The Mathlib leaves for exact
derived functors and cohomological detection remain in use.

No module is withdrawn. Existing declarations and their other consumers remain intact.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically sound. The implementation uses the full lifted
bounded category as already defined, rather than selecting representatives of integer
orbits. The monoid structures for composite and successive lax monoidal functors require
explicit comparison; identifying the underlying additive maps alone is insufficient.
The resulting comparison and normalized ring reconstruction are proved as generic
private helpers before specializing to the concrete Frobenius functor. Explicitly
typed comparison equations avoid expensive unfolding of chosen sheafifications.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
