# Sheaf.Paper.FieldWeilShriekShiftData proof elaboration

## Reason

Repository path: `coord/changes/g8-field-weil-shriek-sequential-elaboration.md`.
The stage-3 lander names a reviewer override of this record
`g8-field-weil-shriek-sequential-elaboration.change.md` in its flat fixes directory.
The returned head `3ed40cb0ebd` passed review but did not land because its reviewer
override was named `g8-field-weil-shriek-sequential-elaboration.md`; that name is
not an accepted override key. This record is included directly in the repaired
packet at the repository path above.

The direct-importer check of the repaired semilinear consumer found that this
unchanged module compiled without Lean errors but took 68.2 seconds. Its profile
spends 34.8 seconds in type-class inference. Sequential elaboration, local
barriers for the completed coefficient constructions, and transparency settings
avoid repeatedly elaborating those constructions. The original context is
retained for the constructible-shift definition and normalization and around the
later proofs that require transparent geometric-fiber computations.

Every existing declaration, statement, proof, definition body, import, visibility
and exported attribute is retained verbatim. No data or target meaning changes;
no hole is added. The preceding packet compiled this module in 42.6 seconds,
but its local reducibility settings also changed exported instance lookup keys.
The current repair scopes the operation barriers inside Finite and restores both
geometric-fiber aliases after that section, before the final shift instances.
The signatures and bodies of those instances are unchanged. The final clean
module compiles in 34.8 seconds. The unchanged QbarCurveDuality,
WeilMixedUpperBounds and WeilShriekShiftCompatibility compile in 33.3, 6.2 and
5.5 seconds respectively. Their temporary verification copies were removed. The initial
shift lemmas use the same coefficient barriers in a separate section. The
geometric-fiber aliases are reducible only during the later operation proofs,
with their original status retained for instance registration and compact-support
normalization.
The module is unclaimed in the current claim snapshot.

## Old

The header had no Elab.async option. After end OpenGeometry the options were:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

No completed-coefficient barriers followed fieldConstructibleShift_normalization.

## New

Add `set_option Elab.async false`. Set both respectTransparency options to true
after end OpenGeometry. After fieldConstructibleShift_normalization add:

```lean
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence HasDerivedCategory.standard
  Scheme.residueField
```

Wrap fieldChainShift_unique, fieldIntegralShift_unique,
fieldIntegralPullShift_existsUnique and fieldIntegralPullShift in an inner
InitialShiftElaboration section. It sets both respectTransparency options to true
and applies the same five local barriers above. The section ends before the
original invertibility variables and fieldConstructiblePullShift, restoring
that declaration and fieldConstructibleShift_normalization's original context.

After fieldRationalPullComp, inside the existing Finite section, restore
abstract pullback functors for the finite operation declarations:

```lean
attribute [local irreducible] constructibleIntegralPullback integralDerivedPullback
  rationalDerivedPullback commonStageDerivedPullback
```

After the private geometric-fiber instances and before FiniteGeometry, add
the following local alias normalization. This lets the recorded geometric fiber
and its literal pullback representation share the same instance keys in the later
proof context.

```lean
set_option allowUnsafeReducibility true in
attribute [local reducible] FiniteFieldDatum.geometricFiber zlFiberMap
```

Before fieldSupport_copy, restore both aliases to local semireducible status:

```lean
set_option allowUnsafeReducibility true in
attribute [local semireducible] FiniteFieldDatum.geometricFiber zlFiberMap
```

The private instance caches are registered with the original alias status, and
the compact-support normalization uses that original status again. This retains
their existing instance lookup keys. After end Finite, repeat the local
semireducible restoration above: ending Finite otherwise restores the reducible
alias context from outside that section. The pullback barriers are scoped inside
Finite, so they also end before fieldZlPullShift, fieldZlShriekShift,
fieldWeilFrobeniusShift and fieldCommonWeilFrobeniusShift are registered. This
preserves the original lookup keys of those exported instances.

Keep the original false settings, scoped to each of these declarations:
fieldLocalizeIso, fieldFrobenius_isEquivalence and fieldWeilShriek_recorded.
The two wrappers inserted before each declaration are exactly:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

## Users

The scheduling option and attributes are local to this module and are not
exported. Their scope nevertheless affects the lookup keys stored when an
instance is registered. The first dry run of this repair found missing Frobenius
CommShift instances in QbarCurveDuality, WeilMixedUpperBounds and
WeilShriekShiftCompatibility; all three compiled on main. Restoring the original
context before registration repairs those keys without adapting any consumer.
No declaration signature or body changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Local elaboration settings only; all declarations and proofs preserved. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Interface unchanged; no adaptation required. |

## Status

landed 20261027T233952-L-4145821 2026-10-27 (merge of deliver/G8/Sheaf.Paper.PodReindexingHomCoefficientDescent)
