## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenRestrictionMixed` in
`lean/Sheaf/Paper/DerivedOpenRestrictionMixed.lean`, preserving its signature and sole
public import. Private proved helpers lift pullback compositor associativity through
exact derivation, establish vertical square pasting, identify the specified derived
direct-image compositor with the adjoint conjugate, and then apply mate pasting.
Validation: `lcompile.py` compiled the final module without warnings in 23.1 seconds.

The initial exact-compositor helpers follow the already-proved sibling module
`DerivedOpenRestrictionSuccessive`; the vertical calculation and conjugate
normalization are proved here. Updated the item's node to this route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenRestrictionMixed`
(node `lem-sfb-derived-open-restriction-mixed`).
Added zero holes; no `sorry` remains in the delivered Lean module. No split-off statements.

## No longer needed

The following original proof dependencies are unnecessary for this item and have been
removed from its `proof_deps`; their modules are not imported:

- `lem-sfb-kinjective-direct-image-open-word-model`
  (`Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel`): exact pullback
  coherence and the existing derived-composition conjugacy theorem suffice.
- `lem-sfb-module-direct-image-open-pasting`
  (`Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting`): use formal mate pasting
  directly, without underived sectionwise open comparisons.
- `lem-weil-pbc-derived-exchange-module-termwise`
  (`Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise`): no representative formula
  is needed, and this declaration concerns constant-ring etale modules rather than
  the internal pro-etale module categories of this item.

No original import was removed: the public data module is needed for the statement.
No existing module or declaration is withdrawn. The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is longer than necessary: the claimed identity is formal for
commutative squares and the specified adjunction-normalized compositors. It requires
neither the open hypotheses nor representative-level exchange normalization. The
public statement retains every original hypothesis.

Delivery tool failure: both normal `deliver3.py V6 Sheaf.Paper.DerivedOpenRestrictionMixed`
attempts refused to push with `COMPILES WITH WARNINGS (local), nothing pushed`.
The warnings are in the cached unpublished dependency `Sheaf.AlgebraicGeometry.SfP1ChartExchange`
from commit `c0c6c1dbd53a01ace3cacf8b04fe35c4221e2554`, at lines 565–566:
unused simp arguments `ordinaryFinitePullback`, `ordinaryFiniteLine`, and
`ordinaryFiniteDegreeZero`. The shared source already separates these reductions
into a preceding `dsimp only` and omits them from that simp list; retry still used
the same old cached revision. The dependency claim names B2. No adaptation is
permitted under the held-module rule because this delivery changes no shared
interface. The item's final standalone compile remains clean (23.1 seconds), and
its complete proof, node update and this report are preserved in the sandbox.
The delivery tool needs to use the corrected dependency revision; nothing was pushed.

Resumed rework verification (2026-10-27): the required initial delivery check again
failed before pushing with the same cached dependency warnings from
`c0c6c1dbd53a01ace3cacf8b04fe35c4221e2554`. The appended axiom probe reached
`SHEAF-PROBED 10`; compilation completed in 19.2 seconds. All three unused simp
arguments are in the cached `SfP1ChartExchange` source, not this delivery.
The current shared source already performs the four ordinary-functor reductions
with `dsimp only` and uses a reduced subsequent simp list. Thus the recorded
dependency revision and diagnostics still do not reflect that corrected source.

The retained public theorem signature matches the quarantined item exactly, and
its original one-hole proof remains completely filled. The failing dependency is
transitively required by the item's sole public statement import, through
`DerivedDirectImageOpenCoherenceData` and its imported source
`ModuleObject.Derived.BoundedConstructible`; deleting an item proof import cannot
remove it. No other module, source-library import, quarantine file, compile cache
or launcher script was changed to bypass this refusal. The delivery tool must
refresh its dependency revision or correctly scope the warning check before this
packet can be pushed.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
