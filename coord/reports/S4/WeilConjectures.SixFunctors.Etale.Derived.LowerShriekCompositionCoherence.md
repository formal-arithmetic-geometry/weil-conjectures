## What changed

Proved `AlgebraicGeometry.Etale.projectionMapAssociativity` from the already proved
`projectionMapOfCompactification_assoc` at the chosen compactification. A private generic
coefficient-category helper rewrites `leftDerivedUpperStarTensorIso_hom`. The predicate and the
existing theorem infer definitionally equal sheaf braidings through different instance paths;
a private metaprogram constructs an explicit heterogeneous-congruence certificate between the
component propositions, checked by Lean's kernel. This avoids unfolding the derived localization.
The helper uses only equality congruence, reflexivity and proof irrelevance. Existing statements,
attributes, public imports and definitions are unchanged.

Added the private proof import
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc`. Updated the existing
`lem-route-projection-map-associativity` node's proof, proof dependencies and proof origin to
match this route, retaining its current statement, provenance and Lean attachment.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.projectionMapAssociativity`
(node `lem-route-projection-map-associativity`). Added zero holes and split off zero statements.
One of the current source module's two holes is closed. The one remaining hole is
`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`
(node `lem-route-exists-right-derived-lower-shriek-comp-iso`), retained verbatim from current
source. The former delivery's application of `rightDerivedLowerShriekCompCoherence` and its
public import were removed because that module is absent from the current source. No replacement
statement or new hole is added.

## No longer needed

No pre-existing import is removed and no module is withdrawn. The associativity proof does not
need these former proof-route nodes:

- `def-sfb-ringed-projection-coherence-data`
- `def-weil-size-convention`
- `lem-kun-derived-pullback-composition-monoidal`
- `lem-pc-kflat-resolution`
- `lem-pur-etale-ringed-projection-identification`
- `lem-pur-kflat-total-tensor-model`
- `lem-sfb-ringed-derived-monoidal-comparisons`
- `lem-sfb-ringed-projection-tensor-associativity`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`

Correspondingly this proof does not import
`Sheaf.Paper.RingedProjectionCoherenceData`,
`Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.KFlatTotalTensorModel`,
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`,
`Sheaf.Paper.RingedProjectionTensorAssociativity`, or
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
No separate Lean attachment exists for the size convention or arbitrary-ring identification
in the current node records. These are route removals only; other consumers may still need them.

Removed the obsolete top-level tool approvals for
`lem-sfb-ringed-projection-tensor-associativity`,
`def-sfb-ringed-projection-coherence-data`,
`lem-sfb-ringed-derived-monoidal-comparisons`, `lem-pc-kflat-resolution`,
`lem-pur-kflat-total-tensor-model`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and
`lem-kun-derived-pullback-composition-monoidal`. Retained the approval for the open-derived-tensor
node, whose canonical open comparison is used by the source theorem. No blueprint unit statement
or realized proof step is bypassed: `sk-prop-sf-cbc` has no realized entries for this node.

The experimental private import of `Sheaf.Paper.FiniteProjectionActionLaws` was removed before
delivery. Its declarations are not used. Composition drafts were never delivered and are not
part of the packet.

## Where the brief, the DAG or earlier work was wrong

The associativity plan is mathematically valid but repeats a proper/open composite calculation
already proved in the adopted source library. The shorter route is specialization of that
source theorem. Direct `exact` or `simpa` is computationally expensive because its braiding
instance differs syntactically from the predicate's. The explicit congruence certificate solves
that conversion without changing any statement or construction.

Repair of return at delivery head `9b03674a948`: reconstructed the module from its current
shared source after the red-batch rollback, then reapplied only the associativity proof and its
private import. Removed the stale public imports of `LowerShriekCompCoherenceStatement` and
`Perfect.SitePerfect`, the stale composition proof, and the earlier `omit [Finite Λ]` modifier.
The existing finite-coefficient binder is preserved. A theorem-scoped
`linter.unusedSectionVars` option suppresses its intentional unused-hypothesis warning. Refreshed the node from current source before applying only the proof,
proof dependencies, proof origin and obsolete tool-approval removals. Its full statement, Lean
attachment and provenance are preserved. No target, definition, public import, existing attribute
or other module changes; no change record or forced adaptation is needed.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
