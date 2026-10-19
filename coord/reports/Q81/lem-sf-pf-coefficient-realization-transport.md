## Worker report

The item is stated in `Sheaf.Paper.CoefficientRealizationTransport`. All theorems
have `sorry` proofs, and all definitions have real data. Only the item's `lean`
record is delivered; no dependency node, natural-language statement, dependency
list, proof, or target changes.

The two numbered return findings are repaired. For Finding 1, the complete reviewed
`def-exchange-projection` record remains unchanged, including its finite-coefficient
pro-etale construction. `ExchangeProjectionInterface.lean` and the dependency-node
copy are removed from this packet. The item module now contains exactly the three
requested helpers, listed in `lean.declarations`: `ExchangeProjectionTransportStage`,
`compactificationExchangeFromTransportData`, and
`compactificationProjectionFromTransportData`. Their docstrings explicitly identify
the verbatim original `ExchangeProjectionStage` and `compactification*FromData`
declarations. Only the names and docstrings differ; the stage fields and two formulas
are unchanged. For Finding 2, the unused required comparisons `push`, `pull'`, and
`push'`, and their `Obj` helpers, are removed. The proper-factor comparisons required
by the four displayed maps remain.

The local six domains are indexed by `Fin 6`, in the order X, bar X, Y, X', bar X',
Y'. `D₀` and `D₁` are precisely these supplied closed coefficient/site domains;
they have independent object and morphism universes between the two systems.
This labels the domains of the fixed compactification square; it makes no
geometric existence or preservation assertion. `system₀` and `system₁` use the
local `CategoryTheory.ExchangeProjectionTransportStage` helper, containing
pullbacks, direct images, adjunctions, tensors, theta, beta, and gamma.
`comparison i` is T on domain i. Every operation comparison is a natural
isomorphism of functors; the three tensor comparisons are natural in both inputs.

Here is the clause-by-clause rendering.

- The supplied comparison functors and invertible pullback, direct-image, and
  open-extension comparisons are the corresponding fields of
  `CoefficientRealizationTransportData`. The tensor comparisons are `tensorX`,
  `tensorBar`, and `tensorY`. `CoefficientRealizationObject` retains the two
  input objects and their supplied isomorphism. Its `map` and `tensor` definitions
  explicitly construct the composite comparisons, including input comparisons.
- `Preserves.unit`, `counit`, `unit'`, and `counit'` require compatibility with
  the actual units and counits of the proper adjunctions. `Preserves.mu` and
  `theta` require compatibility with the actual specified tensor-pullback and
  square comparisons. `Preserves.beta` and `gamma` refer to the actual natural
  open maps from the operation stage, with the specified pullback-composition
  comparison incorporated in gamma, as in the recorded dependency.
- The node's pi is `d.pi`: its maps are the components of the existing
  `Adjunction.rightAdjointProjectionMap`, hence eta followed by pushforward of
  mu followed by epsilon tensor identity. The node's e is `d.exchange`, the
  actual `mateEquiv` of the specified proper square and the two adjunctions.
  The two compactification maps are `d.projection` and `d.compactExchange`,
  using `compactificationProjectionFromTransportData` and
  `compactificationExchangeFromTransportData`; these are the original recorded
  formulas Rp(gamma) pi and Rp'(beta) e, including their functor associators.
- `coefficientRealizationTransport` concludes all four comparison equations for
  every input. No field assumes any of these four conclusions. Each equation
  is `T.map map₀ ≫ target.comparison.hom = source.comparison.hom ≫ map₁`,
  exactly the node's b_t T(m^0) = m^1 b_s in Lean's composition order.
- `coefficientRealizationTransport_map` gives arbitrary operation whiskering by
  naturality of the supplied comparison. `..._tensor` gives tensor whiskering
  in both inputs, including tensoring with identities. `..._comp` gives pasting.
  `CoefficientRealizationPath` and `..._path` express the equation for every
  finite string of such arrows, including both complete base-change routes.
  These statements can equally be instantiated in functor categories, so the
  equations include natural transformations, rather than just unrelated maps.
  For the four maps the comparisons are natural in all inputs, and the main
  theorem quantifies every input component.
- `..._successive` retains the two comparison functors T and S, both intermediate
  equations, and the source and target composition cocycles. Its conclusion
  uses the supplied comparison for T followed by S. `..._identity` retains the
  identity normalizations explicitly. There is no arbitrary Prop standing for
  a cocycle. Conditional refinement uses the same main/whiskering/path statements
  applied to the supplied refinement data: primitive compatibility is required,
  and the finite-string conclusion pastes exactly those squares. No refinement
  comparison is asserted to exist and no unconditional independence is claimed.
- `..._eq_of_eq` states the final forward equality-transport assertion, with
  common endpoints, both intertwining equations, and the original equality.
  It imposes neither faithfulness of T nor invertibility of either arrow.

The source dependency is `def-exchange-projection`, still recorded as
`Sheaf.Paper.ExchangeProjection` /
`AlgebraicGeometry.ProEtale.coefficientExtensionExchangeProjection`. Its full source,
including the finite construction and supplied-domain declarations, was read. The
three local helpers reproduce the precise supplied-domain declarations needed here,
as explicitly requested by the maintainer's return. Direct imports are the upstream
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMap` (using
`CategoryTheory.Adjunction.rightAdjointProjectionMap`) and Mathlib's
`Mathlib.CategoryTheory.Adjunction.Mates` (using `CategoryTheory.mateEquiv`). These
provide the actual mate constructions. The recorded dependency is not rebound to
its abstract portion, and its original finite maps continue to belong to its node.

Edge cases checked: identity comparison functors and identity endpoint comparisons;
empty finite routes, whose maps are identities; tensoring an arrow with an identity
in either slot; zero or noninvertible displayed maps; arbitrary compared input
objects and isomorphic images; independent universes for the two coefficient
systems; successive functors without faithfulness; and absence of refinement
comparisons, where the conditional assertion makes no existence claim. The
refinement qualification and identity cases are retained.

Searches from the saved packet were retained:

- `msearch.py`, leanfinder, "comparison functor transports projection formula
  exchange and compactification composites": eight unrelated comparison/product
  hits; no whole-item match.
- `msearch.py`, loogle, "CategoryTheory.NatTrans.naturality,
  CategoryTheory.Adjunction.map_η_comp_η": zero hits.
- `msearch.py`, grep, "coefficient.*realization.*transport|projection.*exchange"
  in WeilConjectures/SixFunctors: zero hits.
- `rg` over WeilConjectures and lean/Sheaf found the dependency's primitive
  `ExchangeProjectionComparisonPreserves` interface, but no theorem transporting
  all four composites. The exact item id was absent from upstream Lean.
- The current source of `Sheaf.Paper.ExchangeProjection` was read using
  `scompile.py --source`; its full signatures and docstrings were checked.
  Its direct single-file compile reproduced the duplicate declaration failure
  in the imported open base-change module. The exact diagnostic names
  `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`, exported by both
  `ProEtale.UpperLowerStar.Iso` and `ProEtale.FiniteCoefficient.UpperLowerStar.Iso`.
- `rg` for the new public names in Mathlib, upstream WeilConjectures, and the
  side Sheaf tree returned no existing declarations. The three listed helpers
  reproduce the recorded supplied-domain formulas under the explicit authorization of the return; no new independent
  notion or arbitrary replacement map is introduced.

## Maintainer framework fault

The reviewed `Sheaf.Paper.ExchangeProjection` import closure has a reproduced
collision: `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv` is exported by both
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`.
The maintainer's independent return confirmed this is an overlay/framework fault.
Please repair that shared import closure. This packet leaves the dependency module
and node untouched; its item's `lean.note` records the collision and the authorized
local helper arrangement. No dependency modules are delivered.

## Second reading by Q81

No separate worker was started, as instructed by the dispatcher. The maintainer's
independent review remains the independent reading. The author's self-check read
the node and repaired module together. `Preserves` contains only the eight primitive
unit/counit/mu/theta/beta/gamma squares; no composite conclusion is assumed. `pi` is
the actual right-adjoint projection mate, `exchange` is the actual proper-square
mate, `projection` is the pushforward of gamma after pi at the open extension, and
`compactExchange` is the pushforward of beta after exchange at the open extension.
The operation, tensor, pasting, path, successive, identity and forward-equality
statements retain all reviewed clauses and the conditional refinement qualification.
The unused ordinary push/primed-operation comparisons were removed as requested.
The three inserted helper bodies were compared with the recorded originals, after
normalizing their declaration names and removing docstrings; they match verbatim.
The item node was refreshed from current main while retaining only the repaired
`lean` record. No statement correction, new node or dependency-record repair is made.

## Validation

The repaired single module compiled cleanly through the prescribed `scompile.py`
wrapper, both as the sandbox file and at its library module path. The self-check
confirmed the exact main signature, all three helper bodies against the recorded
source, removal of all three unused comparisons and their object helpers, the
100-column limit, and an item-node delta confined to `lean`.
