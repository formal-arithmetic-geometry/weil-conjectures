## What changed

Replaced the body of `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernScalar_pullback`
with a reduction through ordinary scalar association and a derived counit lift.
The theorem's statement and its two public imports are unchanged. The two new proof
imports are `TowerChernOrdinaryScalarPullback` and `TowerScalarPullbackCounitLift`.

`TowerScalarSingleCounit` defines the actual universal scalar counit on singles,
as a composite of natural transformations. Its root component is definitionally
`lineComparison`; no choice or unproved existence theorem enters this definition.
The local endpoint calculation uses naturality of this counit, the derived lift's
square, and naturality of exact pullback's single comparison. This proves both the
coefficient endpoint and the unshifted root endpoint. The proved private lemma
`scalar_shift_endpoint` then expands the composite shift comparisons and transports
the root equation to shift two, producing the exact original target equation.

The ordinary construction and the derived lifting remain separate obligations.
The first constructs ordinary maps and their section normalizations, with no derived
scalar/pullback transformation. The second takes any ordinary association satisfying
the resolving-class hypothesis and lifts it with the counit square on every system;
it assumes and concludes neither coefficient nor root endpoint normalization.
The original theorem combines them by naturality and a genuine shift calculation.
The proof uses explicit conversions between definitionally equal presentations
of the system and derived categories. No public attribute or shared definition
is changed.

## Proved and sorry left

Closed the original syntactic hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernScalar_pullback`
(node `lem-sp-tower-chern-scalar-pullback`).

Added two holes, both exactly `:= by sorry` in named public theorems:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernOrdinaryScalar_pullback`
  (node `lem-sp-tower-chern-ordinary-scalar-pullback`).
- `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_scalarPullback_counitLift`
  (node `lem-sp-tower-scalar-pullback-counit-lift`).

Thus this is a decomposition: one upper hole closed and two strictly smaller
obligations added, not a complete proof without `sorryAx`. The item module contains
zero holes; its three new modules contain two in total. The scalar-single-counit
definition and the private shift lemma contain no holes. The server compiled all
four Lean files; the item compiled in 20.1 seconds. The delivery preflight rechecks
the final packet after removing unused simplifier arguments.

## No longer needed

No original imports were removed and no module is withdrawn. The main node no longer
needs `det-def-sp-tate-twist-locally-free` or
`lem-weil-pbc-derived-single-fully-faithful` for this argument. We compare the ordinary
root tensor maps first and transport them through a counit square; no inversion of
the root scalar counit, compatible root trivialization, or faithfulness of derived
evaluation is required. These removals concern this proof route, not declarations
elsewhere in the library.

The original inverse-image, semilinear-sections, cartesian-roots, ordinary Chern,
coefficient-pullback and line-pullback dependencies remain needed in the ordinary
construction. They have moved below its new node rather than being pruned. The
algebra-diagram coherence tools remain relevant to ordinary association and derived
lifting; the latter now records the specific derived-comparison and K-flat-resolution
dependencies. The intermediate pullback definitions and the Chern/projective
single and shift definitions remain directly used in the main proof.

## Where the brief, the DAG or earlier work was wrong

The previous plan asked to trivialize the whole root tower and identify derived
maps by single full faithfulness. The weaker fact actually needed is the universal
scalar-counit square, which applies even when its root component has not been proved
invertible. This eliminates that local-triviality detour. The generic algebra-diagram
coherence theorem is useful but is not immediately applicable to the fixed tower
coordinates without their ordinary geometric construction and transports.

Checked the new obligations on zero systems, empty schemes and charts, identity
pullback, and the first positive quotient level. The ordinary equations use actual
coefficient multiplication and the given root comparison. The derived lift makes
no flatness assumption on the coefficient map or on arbitrary M: only the resolving
complexes used to define the comparison must be flat-term K-flat, and their images
are explicitly required to be K-flat. In particular, ramified coefficient extensions
and nonflat scheme morphisms have not been excluded. No target, existing statement,
shared definition, or source-library module was changed.

## New nodes

`def-sp-tower-scalar-single-counit` records the explicitly constructed natural
transformation on singles, in `Sheaf.Paper.TowerScalarSingleCounit`.

`lem-sp-tower-chern-ordinary-scalar-pullback` records ordinary inverse image,
scalar association, its resolving-class property, coefficient-unit factorizations,
and the two ordinary endpoint equations, in
`Sheaf.Paper.TowerChernOrdinaryScalarPullback`.

`lem-sp-tower-scalar-pullback-counit-lift` records the counit-normalized derived
lift and its shift compatibility for arbitrary ordinary association, in
`Sheaf.Paper.TowerScalarPullbackCounitLift`.

All three nodes carry the parent's source, explicit proofs in words, actual logged
Mathlib searches, and Lean attachments. The parent's proof and proof dependencies
now follow the implemented calculation. No change record is required because the
packet changes only the item, its node, and new modules and nodes.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
