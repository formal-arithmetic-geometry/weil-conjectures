## What changed

Replaced the hole in `falseProjectionChartTail` by a calculation from the stated
chart cancellation and a strictly smaller geometric exchange-pasting obligation.
The calculation proves the normalized shifted-line square, transports the inverse
line comparison by naturality, carries the arbitrary trace through the pullback
compositor, and proves the constant-unit comparison. The public statement is unchanged.

The coefficient square uses the already proved
`ordinaryFiniteShiftedLinePullback_square`. The constant-unit calculation uses the
proved source-library formula
`leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp`, with explicit bridges
between the concrete and native single-degree comparisons. Generic categorical
helpers do the pasting before specializing to the concrete derived categories.
The final assembly uses the native source shift and cached instances of the trace
definition, avoiding costly conversion of the fully specialized composite.

The proved steps are separated into modules because concrete/native conversion in
the kernel exceeded the 60-second file limit when the steps were checked together.
Every new module has one public statement. All private helpers are proved. No
existing definition or shared interface was changed.

The only residual is `exchangeIsoTransport` for an arbitrary complex M. It contains
no N, annihilation hypothesis, twist transport, invertibility hypothesis on N, trace arrow
or constant-unit comparison. Its docstring and node give the complete canonical
counit-pasting argument. This is a decomposition, not a claim that the geometric
exchange-pasting mathematics is finished.

Corrected the item's own node attachment from the nonexistent `FalseMate` module to
its actual `FalseTail` module and updated its proof route.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Etale.SfP1Transport.falseProjectionChartTail`.
There are zero textual holes left in the item module.

Added one strictly smaller geometric obligation:
`AlgebraicGeometry.Etale.SfP1Transport.exchangeIsoTransport` in
`Sheaf.AlgebraicGeometry.SfP1ExchangeIsoTransport`. Its proof is exactly `by sorry`.
This is the only new holed declaration.

The following new public helpers are proved, all in namespace
`AlgebraicGeometry.Etale.SfP1Transport`:

- `constantUnit_hom`
- `nativeConstant_hom`
- `finiteConstantComparison_hom`
- `unitPullback_native_hom`
- `constantUnit_pullback`
- `middle_exchange`

Holes closed: 1. Holes added: 1. Net: 0; this delivery is a decomposition.
No definition was changed or introduced.

## No longer needed

No existing module is withdrawn. The original public import of
`SfP1ProjectionTraceFalseFactorCancel` is retained because its inverse factor occurs
in the statement and its cancellation theorem is used. Proof imports for the shifted
line square and native unit formula occur in the new proved helper modules. They
remain dependencies of this argument.

The abstract existence theorem in
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
(`lem-sfb-ringed-derived-monoidal-comparisons`) is no longer a direct proof dependency
of the tail node. The unit calculation instead uses the concrete, proved native unit
formula. The residual node names the existing mate-pasting theorem and the precise
mathematical nodes for proper self-exchange and isomorphism-unit normalization.
This does not claim to prune the generic comparison globally.

No diagonal class, supported Ext representative, splitting-family trace
normalization, diagonal integral or target theorem is imported to prove this
arbitrary-trace identity. No existing dependency module is claimed as globally pruned. The preliminary new
`SfP1MiddleProjectionExpansion` helper was not needed: its calculation is combined
with map-factor pasting inside a proved private helper of `SfP1MiddleExchange`.

## Where the brief, the DAG or earlier work was wrong

The old tail node's `lean.module` was
`Sheaf.AlgebraicGeometry.SfP1ProjectionTraceFalseMate`, absent from the current source,
although its `lean.file` and declaration correctly identified this tail. This packet
repairs its own attachment. The factor-cancellation node also records `FalseMate`
while its declaration is in `SfP1ProjectionTraceFalseFactorCancel`; that unrelated
attachment is reported here and is not changed.

An abstract existence of normalized ringed comparison systems does not itself
identify the chosen ordinary etale `pushPull`. The residual keeps that specific map
and the chosen proper exchange as explicit endpoints.

The old tail plan grouped coefficient normalization, exchange pasting and the
constant-unit comparison together. The coefficient square follows from an existing
proved public declaration, and the unit comparison from the proved native unit
formula. Only exchange pasting remains. The existing nodes
`lem-sf-proper-self-exchange-forget-supports` and
`lem-sf-iso-pushpull-unit-normalization` state the needed mathematical normalizations.
Their proved Lean declarations landed during this session, in
`ProperSelfExchangeForgetSupports` and `SfIsoPushPullUnitNormalization`. They remain
explicit dependencies of the residual proof plan and are not duplicated as extra holes.

The unit's statement and realized proof route are unchanged. The new residual and
the categorical calculations work for the empty base and the zero coefficient ring;
no nonemptiness, positivity or Noetherian assumption was added.

## New nodes

All seven nodes are in `dag/nodes/sec-six-functors-basics/`; their modules are in
`lean/Sheaf/AlgebraicGeometry/`. No change record is needed: only the item and new
modules/nodes are changed.

`lem-sf-p1-exchange-iso-transport`, module `SfP1ExchangeIsoTransport`: the one
remaining geometric exchange-pasting theorem, for an arbitrary projective-line complex.

`lem-sf-p1-constant-unit-hom`, module `SfP1ConstantUnitHom`: proves that the
specified constant-unit comparison is the native single-unit comparison.

`lem-sf-p1-native-constant-hom`, module `SfP1NativeConstantHom`: proves the
single-degree inverse-image comparison for a constant sheaf, for general coefficients.

`lem-sf-p1-finite-constant-comparison-hom`, module `SfP1FiniteConstantComparisonHom`:
proved specialization of the previous identity to the finite coefficient category.

`lem-sf-p1-unit-pullback-native-hom`, module `SfP1UnitPullbackNativeHom`: identifies
the specified ordinary unit pullback with the native single-constant comparison.

`lem-sf-p1-constant-unit-pullback`, module `SfP1ConstantUnitPullback`: proves
compatibility of constant-unit comparison with inverse image using the native unit formula.

`lem-sf-p1-middle-exchange`, module `SfP1MiddleExchange`: proves the shifted-line
coefficient square and combines it with the geometric residual to give the middle equation.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
