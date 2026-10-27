## What changed

Replaced the hole in `WeilConjectures.IntegralOnSlice.qcqsOrdinaryRestrictionExact`
with a proof from two strictly lower algebraic inverse-image comparisons. The item
statement, independent universes, and all qcqs hypotheses are unchanged.

The actual constant-section finite ring maps are identified with isomorphisms from
uniqueness of the constant-sheaf adjunction. The proof includes the comparison that
forgets commutativity, its sheafification-unit equation, and naturality for quotient
transitions. A natural isomorphism of finite coefficient diagrams and preservation
of the inverse limit give an isomorphism of cone points. Transposing the specified
finite projection equations identifies that morphism with `ordinaryCoefficientMap`.
This identification is proved for the specified completed ring map.

For compilation, the constant-ring comparison is proved once for an abstract
commutative ring and specialized to the quotient rings. Direct private instances
supply ring, commutative-ring and abelian weak sheafification, avoiding repeated
search through the essentially small site construction. This changes no public API.

For the weakly etale factor, the map/base-change adjunction identifies inverse image
with sectionwise restriction. Composition uses the actual direct-image composition
comparison and uniqueness of left adjoints. The module result follows by reflecting
limits through the underlying abelian sheaf functor.

Added three new modules, with their nodes, for the independent-universe immersion
ring/abelian inverse-image limit theorem and the arbitrary-coefficient module/abelian
comparison, together with the proved finite constant-coefficient adjunct step.
The two algebraic comparisons concern ordinary inverse image and do not mention
completed coefficients, the prime, the field, or the item theorem's conjunction.
The finite-map theorem is a strictly lower step for any scheme morphism.
No existing module besides the assigned item is changed.

The final four-module compile passed without errors or warnings. The two new
geometric modules took 0.2 and 1.0 seconds from the compile cache; the finite-map
module took 51.0 seconds and the item took 51.3 seconds. Both geometric modules
also passed uncached compiles earlier (under 4 and 33 seconds respectively).

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.IntegralOnSlice.qcqsOrdinaryRestrictionExact` (node
`lem-fix-qcqs-ordinary-restriction-exact`). Its assembly proof and its private helpers
have no holes.

Added one hole, the entire proof of the following public theorem in its own module:

- `AlgebraicGeometry.Scheme.proEtale_immersion_algebraicInverse_limits`, node
  `lem-fix-proetale-immersion-algebraic-limits-universes`.

The new public theorem,
`AlgebraicGeometry.Scheme.proEtale_ringedPullback_underlying_of_isIso`, is proved
from the existing small-site inverse-image action/adjunction and forgetful comparison.
It has no hole. Its proof constructs the transported ring presentation, checks its
unit, transports the module adjunction using an explicit sectionwise direct-image
isomorphism, and cancels the site equivalences.

`WeilConjectures.IntegralOnSlice.ordinaryFiniteCoefficientMap_isIso` is also proved,
with no hole, in `Sheaf.Paper.QcqsOrdinaryFiniteCoefficientMaps`.

This is a decomposition, not an unconditional proof: 1 original hole closed,
1 lower hole added, 0 holes remaining in the item module. The geometric statement
has no module or completed-coefficient assertion; the proved module statement is a natural
underlying-sheaf comparison for arbitrary rings and any morphism, under an invertible
coefficient adjunct, with no limit-preservation conclusion. The finite-coefficient,
transition, completed-coefficient, weakly etale, composition and limit-reflection
arguments are Lean proofs in the item and its proved finite-map helper module.

## No longer needed

No original import was removed: `Sheaf.Paper.QcqsCompletionOrdinaryModels` supplies
all the fixed ordinary constructions in the unchanged statement.

The item no longer directly needs `lem-pur-site-restriction-module-adjunction-exact`
(`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`) or
`lem-weil-proetale-weakly-etale-localization`
(`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`). The weakly etale limit
argument is proved directly from the map/base-change sheaf adjunction.

`prop-weil-pbc-proetale-constant-ring-map`
(`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`) is not needed by this proof:
the actual independent-universe sheafifications admit a direct constant-adjunction
argument, which requires no comparison to the finite continuous-function model.

The old same-universe `lem-weil-pbc-proetale-immersion-limit-preservation` is not
applied directly. Its geometric argument is the source route of the new immersion
step. The restriction/Zariski-local and algebraic-lift dependencies remain below
that step; no global withdrawal or removal of their modules is claimed.
`lem-weil-pbc-module-sheaves-limits-sectionwise` remains used. No unit route changes.

The new module comparison does not need the old fixed-universe
`lem-weil-pbc-proetale-model-ring-presentation`: its actual unit is proved directly
from uniqueness of the supplied ring adjunction and the generic forgetful comparison.
The generic module inverse-image action/adjunction remains used.

## Where the brief, the DAG or earlier work was wrong

The listed geometric and module comparisons have fixed same-universe signatures.
They do not specialize to the item's independent scheme and coefficient universes.
Enlarging the site presentation alone does not make their Lean statements applicable.
The two new statements isolate exactly those algebraic comparisons; the completed
coefficient identification is proved using the prescribed maps.

The checked edge cases are the empty source or target, the zero ring sheaf, the
identity morphism, and the empty indexing category. The new statements exclude none
of these cases. Invertibility of the ring adjunct is explicit in the module comparison;
a general scalar extension would change the underlying abelian sheaf and cannot be
used in its place.

## New nodes

`lem-fix-proetale-immersion-algebraic-limits-universes`, in
`Sheaf.AlgebraicGeometry.ProEtaleImmersionAlgebraicLimitsOfUniverses`, records the
immersion inverse-image limit step for independently sized ring and abelian sheaves.
Its source is Stacks Tags 09AA, 09BL and 00YV.

`lem-fix-proetale-ringed-pullback-underlying-universes`, in
`Sheaf.AlgebraicGeometry.ProEtaleRingedPullbackUnderlyingOfUniverses`, records the
scalar-action/abelian comparison for arbitrary ring sheaves and any morphism.
Its source is Stacks sites-modules.tex, Tags 03D2 and 03D3. This node is proved,
including the transport of adjunctions between the small models and actual sites.

`lem-fix-qcqs-ordinary-finite-coefficient-isos`, in
`Sheaf.Paper.QcqsOrdinaryFiniteCoefficientMaps`, records the proved finite-map
adjunct step for the actual independent-universe ordinary models. Its source is
Stacks sites.tex, example-constant-sheaf, and sites-modules.tex, section-constant.
This proof was moved to its own module after profiling and reducing repeated
sheafification searches and quotient-ring expansion; the combined file remained
above 60 seconds. No additional hole was introduced by the move.

All three nodes include the source argument, exact Lean signature, logged semantic
and source searches, and blueprint ancestry. The whole imported blueprint was searched;
no duplicate actual independent-universe interface was found. The existing
`prop-weil-pbc-proetale-constant-ring-map` is the related finite continuous-function
model statement, with a different Lean coefficient interface.
No definition or statement was changed, so no change record is needed.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
