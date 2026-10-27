## What changed

Constructed the natural system comparison by applying coherent reduction to a normalized
pullback realization and then applying the whole-system adjunction counit.
`effectiveQuotientModelDescent` supplies invertibility of that counit. The comparison is
restricted to the constructible category and its evaluations are computed by the finite
projection lemma. The original theorem statement and reduction-isomorphism definition
are unchanged.

Removed the unused public import of `IntegralPullbackComposition` from
`IntegralComparisonSequenceSystems`: importing a composition theorem into the sequence
constructions created a cycle when proving the lower system-comparison theorem from
normalized realizations. All sequence declaration signatures remain unchanged. Local
transparency settings control the cost of the existing proofs.

Change record: `coord/changes/C4-sequence-comparison-import-direction.md`.

## Proved and sorry left

Original item: one hole, `WeilConjectures.integralPullbackSystemComparison`.
Its assembly proof now has no `sorry`.

The packet currently adds one hole:
`WeilConjectures.integralPullbackCounitProjection`, node
`lem-pod-integral-pullback-counit-projection`. This is only the finite map-normalization
calculation. It asserts neither invertibility nor existence of a natural system
comparison. The system comparison is constructed and its invertibility proved separately
in the item module. Thus the current packet is a decomposition: one upper hole closed,
one strictly smaller hole added; net zero holes closed.

No holes are added in definitions or private helpers. The sequence module has zero holes.

## No longer needed

Removed import: `Sheaf.Paper.IntegralPullbackComposition` from
`Sheaf.Paper.IntegralComparisonSequenceSystems`. Its own statement still needs the item;
no declaration or module is withdrawn.

The item does not separately import or reprove the following planned dependencies:
`prop-weil-pbc-proetale-constant-exact`, `lem-coef-semilinear-derived-sections`,
`lem-pur-kflat-change-of-rings`, `lem-sfb-successive-derived-quotient-normalization`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`def-pur-integral-derived-operations`, `lem-weil-proetale-countable-products-exact`,
`lem-weil-strict-roos-comparison`, `lem-pur-integral-operations-well-defined`,
`lem-coef-normalized-dvr-effectivity`,
`lem-weil-pbc-proetale-derived-pullback-composition`, and
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`.
The normalized realization, effective quotient descent, and finite projection interface
package those calculations. Some remain transitive dependencies of those interfaces;
this delivery does not claim to withdraw them or erase their upstream declarations.
The coefficient evaluation calculus and constructibility theorem are still used.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing sequence-system module publicly imported the higher integral composition
theorem although its declarations do not use it. That import direction prevented the
realization-based proof of the present lower theorem. The import repair preserves all
constructions and checks the current direct consumers in the change record.

The original dependencies did not expose the final finite projection calculation as a
separate declaration. The new node isolates that calculation from the genuine natural
isomorphism construction and its invertibility argument. No statement is disputed.

## New nodes

`lem-pod-integral-pullback-counit-projection`, module
`Sheaf.Paper.IntegralPullbackCounitProjection`: finite evaluation of normalized
realization followed by the coherent counit equals the scalar adjunct of the actual
pullback-tower Roos projection, transported by the prescribed finite pullback model and
reduction counit. This is the map calculation in Stacks Tags 0941 and 099N(5).
It includes arbitrary good representatives, the identity and empty-scheme cases,
and n=0 (coefficient exponent one). Its docstring and node give the complete argument.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
