## What changed

`Sheaf.Paper.SectionPullNormalizationTransport` constructs all three normalization
witnesses explicitly. The restriction/pushforward isomorphism transports the proved internal
`CondensedRing.comapLowerStarIso` through the canonical scalar-restriction and
geometric lower-comparison isomorphisms. Its fully faithful preimage is identity
on sections: first on the essential image, using the component equations, then
on every section module, using naturality with the equivalence counit. The ordinary
pullback comparison is the inverse conjugate under the two composite adjunctions.
The derived comparison is the fully faithful preimage of the supplied internal
isomorphism conjugated by the endpoint and geometric realization isomorphisms.
The realization equation is proved by evaluating map_preimage and cancelling
isomorphisms. No definition selects data from an unproved existence statement.

The only remaining argument, the K-flat computation equation, is isolated in
`Sheaf.Paper.SectionPullComputationOfRealization`. It takes the already constructed
ordinary and derived maps, with their normalization equations, as inputs and proves
one representative equation. This is a strict substep: it neither constructs the
three isomorphisms nor proves the all-object realization equation. The main theorem
combines that substep with the explicit constructions and complete Lean proofs.
Private component lemmas give the section maps of scalar restriction, geometric
pushforward and the section equivalence, and use the proved internal comparison
equations rather than unfolding the geometric coefficient-map construction. No definition or
compile-time limit is changed.

The proof imports `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` and
`Sheaf.CategoryTheory.InternalSectionScalarAdjunction` with `import all` to use
their proved private component formulas, and imports the new computation module.
All existing public statements and public imports are unchanged. No other existing
module is adapted. The two DAG records follow the implemented argument.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.ProEtale.QuotientChange.section_pull_normalized_of_normalized`
(node `lem-sfb-section-pull-normalization-transport`).

Added exactly one hole:
`AlgebraicGeometry.ProEtale.QuotientChange.section_pull_computation_of_realization`
(node `lem-sfb-section-pull-computation-of-realization`). Its complete source-based
proof plan is in its docstring and node. The item module has zero remaining holes;
the packet has one. This is a decomposition: one upper hole closed and one strictly
smaller hole added, net zero holes closed. It is not reported as an independent proof
of the original normalization result.

The private identity-on-sections construction, ordinary conjugate equation, derived
comparison construction, and all-object realization equation have complete proofs.
Validation: the new computation lemma compiled independently, and the optimized
complete main proof compiled in 46.5 seconds with profiling enabled. Profiling
options were removed before delivery. The component calculation uses a scoped
800000-heartbeat allowance for nested section-functor definitional equalities;
the 60-second compile-time limit is unchanged. The complete packet is checked
by deliver3 before push.

## No longer needed

No original imports were removed and no existing module is withdrawn.
`lem-sfb-kflat-scalar-comparison-normalization` is removed from this item's proof
route: rather than construct d by K-flat descent and then identify it with b,
construct d directly from b through the section equivalence. What remains is the
representative equation obtained by pasting the supplied normalization equations.
This does not assert that the generic K-flat theorem is unused elsewhere.

The two other original proof dependencies,
`lem-sfb-internal-section-scalar-adjunction` and
`lem-pd-section-derived-pushpull-normalization`, remain in the new representative
lemma's proof plan. They have not been pruned from the argument.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan chooses a descended d and then
identifies its realization with the supplied b. The implemented route reverses
these tasks: construct d by equivalence, prove its realization equation formally,
and leave only its representative computation equation. This avoids a separate
K-flat-resolution argument for equality on all derived objects.

The generic K-flat comparison normalization theorem has equal site object and
morphism universes, while these scheme sites have objects in u+1 and morphisms in u.
It does not apply directly at the displayed interface. No universe or definition
of the item was changed to force it to apply.

Edge cases considered: identity coefficient or scheme maps, zero coefficient
rings, zero complexes, and empty schemes. The constructions use only identity
section maps, composite adjunctions, and equivalences. The remaining equation
uses coefficient compatibility and computation counits, with no flatness
hypothesis on the coefficient map or boundedness hypothesis on complexes.

## New nodes

`lem-sfb-section-pull-computation-of-realization` records the representative
computation substep in `Sheaf.Paper.SectionPullComputationOfRealization`. It has
all comparison isomorphisms and the realization equation as inputs and concludes
only the computation equation on flat-term K-flat section complexes. The section
and geometric normalization equations in the existing dependencies are the source
of its proof plan. No change record is needed: no existing signature or public
definition changed.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
