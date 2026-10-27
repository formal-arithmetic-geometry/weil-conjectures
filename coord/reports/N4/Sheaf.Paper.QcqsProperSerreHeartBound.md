## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.exists_uniform_serreHeart_bound_of_isProper`
in `Sheaf.Paper.QcqsProperSerreHeartBound`, with its statement, coefficient disjunction and
universes unchanged. Choose the bound `2 * e + 2` from the existing finite-type fibre bound.
Pullback preserves the generated heart class by exactness, coproduct preservation and the
proved `stratified_pullback` helper from `FiniteConstantStratifiedZariskiLocality`.
Apply the existing proper closed-fibre rigidity and profinite geometric-family estimate.
Exact evaluation on w-contractible affine tests then commutes with derived pushforward
and homology; the covering basis detects zero sheaves. Six proved private helpers implement
this glue. No existing definition or public interface changes; no consumer adaptations.

The node copy records this route. Proof imports add rigidity, the family estimate,
constructibility locality (using `import all` solely for its proved private pullback helper),
object-property kernel/cokernel closure, field-base-change dimension, exact w-contractible
sections, and the proved ring-equivalence helper for w-contractibility.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.exists_uniform_serreHeart_bound_of_isProper`
(node `lem-sfb-qcqs-proper-serre-heart-bound`). The item contains zero `sorry`; zero holes
are added and zero statements are split off. The proof uses existing stated dependencies,
including `proper_wContractible_closedFibre_rigidity`; it does not claim those dependencies
have all been independently proved here.

## No longer needed

Removed these original direct proof imports:

- `Sheaf.AlgebraicGeometry.DimensionExtension`: the proved
  `WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension` inequality suffices;
  node `lem-kun-dimension-extension` is unnecessary for this proof.
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`: the instances in the publicly
  imported `UpperLowerStar.Defs` already give the needed exactness;
  node `det-prop-sfb-module-pullback-exact-main` is not needed as a separate theorem.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` and
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: already publicly available
  through the unchanged statement imports, so their duplicate direct imports are removed.
- `Sheaf.AlgebraicGeometry.BoundedComplexDirectImagePresheaf` and its node
  `lem-pe-bounded-complex-direct-image-presheaf`: exact target evaluation gives the
  derived comparison directly, without sheafification of a cohomology presheaf.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` and its node
  `lem-sfb-internal-module-operations-transport`: no section-ring equivalence is used.
  The abelian clauses of the exact-sections theorem suffice; its unused ring argument
  is instantiated with a constructed constant ring sheaf.

The direct dependencies `lem-sfb-alpha-iso` and
`lem-weil-pbc-constructible-preimage` are replaced by the already proved stratification
pullback helper in `lem-sfb-constructible-zariski-locality`; their mathematical content
is encapsulated there, rather than reproved here. Removed obsolete top-level approved
`tool_uses` entries: `lem-kun-dimension-extension`,
`det-prop-sfb-module-pullback-exact-main`, `lem-sfb-alpha-iso`,
`lem-pe-bounded-complex-direct-image-presheaf`, and
`lem-sfb-internal-module-operations-transport`.

No module is withdrawn. These are dependency removals for this item only: other consumers,
including the rigidity module, may still need them. No declaration under
`lean/WeilConjectures/` is edited or removed. The unit's own realized route is preserved.

## Where the brief, the DAG or earlier work was wrong

The five-step plan is mathematically usable; its final presheaf/transport step is longer
than necessary. W-contractible evaluation is exact, and the existing exact-right-factor
composition isomorphism identifies derived evaluation with evaluation of derived image.
The field-extension equality in Step 1 can be replaced by the available dimension upper
bound. The qcqs case of the constructibility definition permits reuse of the proved
stratification pullback helper. No disputed statement or definition repair was needed.

Short-route searches used leanfinder, loogle and grep through msearch, plus local rg;
none supplied the complete uniform proper estimate. The resulting proof combines the
existing geometric inputs rather than introducing an equivalent replacement hole.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
