## What changed

Proved the scalar-comparison argument from the existing ringed-topos composition
and K-injective-resolution declarations. Constructed the global-sections ringed
topos morphism using the constant-sheaf adjunction and the integer structural
map. Its module comparison is lifted from the underlying set comparison using
naturality with biproduct inclusions and projections. Exact punctual evaluation
transports the composition theorem's quasi-isomorphism to ordinary global
sections. The derived universal property constructs the normalized comparison;
K-injective resolutions establish invertibility and the representative formula.

The coefficient category remains the original abbreviation with native instances.
Restriction and sections functors use ordinary definition boundaries. Complex sections
is the termwise lift of the same sections functor. The statement displays canonical
underived transport isomorphisms in its unit equation, resolution formula, cocycle and
identity law. Their compatibility is proved by lifting the underlying sheaf identities.
The proposition `CoefficientSectionsGeometry` names exactly the previous geometric
clause and avoids repeating the geometric clause during final assembly.
This is a presentation repair, with all original hypotheses and mathematical conclusions
retained. The change record is
`coord/changes/T6-derived-sections-reducibility.md` and audits all six DAG citers.
The public filtered-colimits import supplies small-site abelian instances formerly
inherited through the removed singleton-site module. No source-library file or
Challenge statement changes. The six consumer modules are being checked unchanged.

The complete item compiled with output artifacts in 56.9 seconds. The unchanged
acyclic-resolution consumer compiled in 54.7 seconds after restoring the native
coefficient category. The Leray consumer's missing finite-limit API is supplied by
the explicit instance. The other four consumers compiled unchanged. Final delivery
checks verify the clean packet. The first delivery attempt timed out and pushed nothing.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.CoefficientDerivedSections.derivedSectionsScalarCoherence`
(node `lem-coef-derived-sections-scalar-coherence`).
The proof constructs the geometric morphism, proves the scalar comparison and its
uniqueness, invertibility and representative formula, and proves both coherence laws.
Holes closed: 1 of 1. Holes added: 0. Holes left in the item: 0. No split-off statements
or new nodes. Existing named proof-dependency theorems are used as intended by stage 3.

## No longer needed

The proof does not use the general singleton-site tensor or derived equivalence
`lem-weil-pbc-singleton-site-module-comparison`. Ordinary punctual evaluation,
the bottom-topology sheaf equivalence, and exactness of the module forgetful
functor suffice for the required comparison and quasi-isomorphism transfer.
Its statement dependency remains in the node as context for the original
mathematical formulation; its proof dependency, proof-step use, and obsolete
`tool_uses` entry are removed.

Removed direct imports of `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
and `Sheaf.CategoryTheory.SiteCoveringAxioms`, and the public import of
`Sheaf.ProperBaseChange.SingletonSiteModuleComparison`. Their interfaces are
not used by this proof. No module is withdrawn. The general ringed-topos composition theorem, restriction
as module direct image, induced-module construction, and K-injective resolutions
remain necessary.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. The general singleton-site derived
equivalence planned in the node is stronger than this proof needs. The proof
steps and dependencies now describe the more direct punctual calculation.

The launcher paused this session to shorten the compile queue and reset its
recorded start time from 1792758586.2194183 to 1792769087.0696557. The worker did
not edit the budget files. Interrupted compile results were checked on resumption.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
