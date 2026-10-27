## What changed

Filled `CategoryTheory.RingedRestrictionLimit.ringedRestrictionStrictLimitCoherence` in
`Sheaf.Paper.RingedRestrictionStrictLimitCoherence`, preserving its complete signature and
all existing public definitions. Private proved helpers construct the sections comparison
from the geometric adjunction, descend the restriction map by the right-derived universal
property, and construct normalized evaluation and inverse-limit comparisons. The proof
checks the restriction identities on K-injective representatives and descends equality of
natural transformations. Strict Roos derivation and uniqueness give the Roos comparisons;
factoring a strict augmentation through the ordinary limit proves its compatibility.

The existing split-transition acyclicity argument is generalized privately to the independent
derived-category universe and the exact-product target category required by this statement.
Local irreducibility attributes prevent elaboration from unfolding derived-functor constructions.
A private structure packages the fixed comparisons and their coherence proofs.
Projection identities are checked on ordinary diagrams before applying them to complexes.
The ordinary-limit unit universal property is transported along its existing functor isomorphism.
The node's proof, proof dependencies and proof origin follow this argument.
The ordinary-limit-of-complexes transport is reused from
`Sheaf.Paper.ExactProductFunctorRoosResolution`; its node is retained as a direct proof dependency.

## Proved and sorry left

Closed the one original hole in
`CategoryTheory.RingedRestrictionLimit.ringedRestrictionStrictLimitCoherence`
(node `lem-sfb-ringed-restriction-strict-limit-coherence`).
Added zero holes. No `sorry` remains in this module, and no new module is introduced.
All private helper declarations are proved.

Validation: the complete module compiled cleanly with normal linting in 32.9 seconds.
The original public definitions and the theorem signature were compared against the source
and remain unchanged. There are no lines exceeding 100 characters.

## No longer needed

The proof does not need direct imports of
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitAcyclic`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.CategoryTheory.DiagramSiteRealization`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
`Sheaf.CategoryTheory.StrictRoosComparison`, and
`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
No import from the assigned source was removed; all public imports are preserved.

The proof no longer directly follows these original DAG dependencies:
`lem-weil-pbc-diagram-site-realization`, `prop-pur-kinjective-resolutions-exist`,
`lem-weil-tower-category-levelwise-abelian`,
`lem-weil-pbc-right-adjoint-preserves-kinjective`,
`lem-weil-pbc-termwise-adjunction-homotopy`, `lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-right-adjoint-preserves-limits`,
`lem-weil-ringed-tower-pushforward-limit-acyclic`, and
`lem-weil-strict-roos-comparison`. Their obsolete top-level `tool_uses` entries are removed.
The existing universal comparison helpers replace separate diagram-site and derived-Hom
constructions. Split-transition acyclicity handles the images of K-injective towers directly.
Strict Roos derivation replaces the separate constant-tower normalization argument.
These are removals from this node's direct proof plan: existing upstream declarations and
transitive dependencies are preserved. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged. The original plan's individual resolution and
constant-tower calculations are unnecessary once the normalized unit equations are proved
on all complexes. The private coefficient-sequence acyclicity helper fixes a derived-category
universe and an abelian-group target; it cannot be applied verbatim with this theorem's
independent universe and the inverse-image target. The private generalization proves the
needed version by the same split-transition and homotopy-equivalence argument.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
