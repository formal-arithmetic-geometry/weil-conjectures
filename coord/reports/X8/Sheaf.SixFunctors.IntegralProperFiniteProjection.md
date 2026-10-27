## What changed

Added the explicit adjunction calculation for `integralProperFiniteProjection` and isolated
its two normalization steps in `IntegralFinitePullbackNormalization`
and `IntegralFiniteProperMate`. The latter is proved by generic adjunction identities;
the former remains as one good-complex lemma. Added the finite coordinate definitions in
`IntegralFinitePullbackCoordinates`. The item retains both original public imports verbatim; all its added imports are private proof imports. No other existing Lean module changes. The original definition body and theorem
statement are byte-identical to the quarantined source.

## Proved and sorry left

One original hole is closed by reduction: `integralProperFiniteProjection`. Its proof uses
`integralFinitePullback_onGood`, `integralFiniteProperMate`, and the existing
`DirectEvaluation.counit` equation. `integralFiniteProperMate` is proved by explicit
adjunction calculations. One hole is added: `integralFinitePullback_onGood`
(node `lem-sf-integral-finite-pullback-normalization`). Thus this packet is a decomposition
with net hole change zero, not a sorry-free proof. The item module itself has zero holes.
No definition contains `sorry`. The finite coordinate module, finite mate theorem,
and good-complex statement have compiled individually; the generic assembly and
transport lemmas were also compiled separately in scratch modules. Final packet
compilation and delivery checks are recorded by the delivery tool.

## No longer needed

No existing public import was removed, and no module is withdrawn. The top theorem
no longer uses the derived scalar adjunction node directly: its finite geometric
adjunction proof uses the smaller finite proper mate lemma. The scalar adjunction
remains needed by the canonical scalar comparison definitions. The K-injective
proper-projection computation and `counit_projection` substitution in the original
one-step proof plan are replaced by transposing through the finite geometric adjunction;
all geometric normalization now occurs on left adjoints before reconstruction.
The canonical bridge, integral coefficient comparison, integral operations, scalar
pullback complex normalization, and coefficient evaluation calculus remain needed.
The normalization proof plan uses the already-proved
`lem-sf-scalar-pull-coefficient-complex-normalization` as a tool from
`sk-rem-sf-pf-done`: it identifies the scalar comparison on cochain representatives.
No theorem of this unit supplies that cochain normalization; the unit route itself
still uses its prescribed coefficient comparisons and geometric adjunctions.

## Where the brief, the DAG or earlier work was wrong

The original one-step DAG proof hid two independent adjunction normalizations. They are
strictly smaller: the first has one good K-flat representative and no direct image, and
the second has one arbitrary integral object and no coefficient system or realization
model. The top theorem is now an explicit mate calculation rather than an unexpanded
appeal to the sectionwise projection equation.

The shared DAG already has a cycle from this item through
`lem-pur-compact-support-integral-coefficient-comparison`, the strict scalar/proper
composition nodes, and integral realization back to this item. This cycle exists
before the packet. Here only the explicit definitions `scalarPull`, `properComparison`,
`finiteReductionIso`, and `finiteDirectImage_eq` of that module are used; its broad
`integralCoefficientComparison` package theorem is not used. The new records cite the existing definition owners
`def-sp-coefficient-mate-comparisons` and
`def-pur-finite-compact-support-scalar-data` instead of the broad package theorem.
The original statement dependency is preserved; no other item's node is changed.

## New nodes

`def-sf-integral-finite-pullback-coordinates` records the actual finite pullback and scalar
pullback coordinate definitions. `lem-sf-integral-finite-pullback-normalization` records
the good-complex reduction/pullback equation. `lem-sf-integral-finite-proper-mate` records
the finite proper scalar comparison's geometric mate equation.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
