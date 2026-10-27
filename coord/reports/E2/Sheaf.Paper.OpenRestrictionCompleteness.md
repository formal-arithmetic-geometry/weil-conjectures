## What changed

Filled `WeilConjectures.OpenRestrictionCompleteness.openRestrictionComplete` in
`Sheaf.Paper.OpenRestrictionCompleteness` without changing its signature, universes,
hypotheses, definitions, attributes, or public imports. Added private proved helpers
for product-preserving principal-cone comparison, the arbitrary-representative
completeness criterion, projection of the completed uniformizer, and transport of
scalar endomorphisms through the given coefficient equivalence.

The proof uses the existing principal-cone local criterion and the normalized
Roos/intrinsic completeness equivalence. Ordinary restriction is right adjoint to
extension, hence preserves the countable products in the cone model. Its coefficient
map preserves the actual completed uniformizer: each projection reduces this claim
to `finiteConstants`. The supplied equivalence's functor equation and counit
naturality then identify the restricted scalar chain map. The resulting comparison
preserves the specified zero-homotopy unit. Exact derived-functor naturality
transfers its invertibility, proving target completeness and invertibility of the
actual completion unit.

Updated the item's DAG proof, proof dependencies, and proof origin to this route.
No definitions or consumer modules were changed. The proof does not require a
nonempty open, regularity of an arbitrary complex, or preservation of K-flat
representatives. The empty open and identity open use the same argument.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.OpenRestrictionCompleteness.openRestrictionComplete`
(node `lem-sf-open-restriction-completeness`).

No holes added or split off. No `sorry` remains in the delivered module. All private
helpers are proved. This is a proof from existing library declarations, including
the existing completeness criteria; it does not claim those dependencies have no
transitive holes.

## No longer needed

The original direct proof dependencies
`lem-sf-immersion-completed-pullback-comparison`
(`Sheaf.Paper.SfImmersionCompletedPullbackComparison`) and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
(`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`) are not needed by this
proof. Principal cones give an arbitrary-complex model, avoiding the geometric
K-flat tensor-pullback comparison. These nodes and modules are not withdrawn;
other library declarations may still need them.

No original imports were removed. Every added import is private and supplies proof
APIs: the principal-cone comparison helpers, slice completion/localization helpers,
Roos completeness equivalence, coefficient datum, principal-cone local criterion,
and existence of an auxiliary prime distinct from ell.
The DAG cites the existing definition owner `def-sf-integral-open-operations`,
not the downstream existence theorem in the same Lean module. The principal-cone
comparison is proved for a product-preserving additive functor, rather than applying
the equivalence-only public theorem to restriction.

## Where the brief, the DAG or earlier work was wrong

The original planned route is unnecessary. The existing arbitrary-representative
principal-cone criterion supplies a shorter route with the fixed coefficient
operations and independent universes. No statement was disputed or repaired.
The unchanged theorem docstring describes the old quotient/K-flat proof plan;
the updated DAG and the proof above record the implemented principal-cone route.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
