# WeilConjectures.PointPullbackRepresentative.reductionCounit

## Reason

The untyped four-level choice projection exposes a large dependent category-instance
signature whenever its computation is used. Direct specializations repeatedly exceeded
the file limit. Use the existing normalized `scalarReductionCounit` interface to the
same canonical scalar-extension witness. This changes the presentation, not the counit.
The two existence definitions have identical bodies; proof irrelevance identifies their
derived-existence fields, so the selected functor and natural transformation are
literally definitionally equal, not merely related by an unspecified isomorphism.

A standalone server check of the following equality compiled in 17.2 seconds:

```lean
private theorem counit_is_recorded (Y : Scheme.{t}) (n : ℕ) :
    scalarReductionCounit l E Y n =
      ((unrestrictedIntegralReductionExistence l E Y n).choose_spec.choose_spec.choose_spec
        |>.choose_spec.2.2.choose_spec.choose) := by
  rfl
```

The checked context uses independent site/coefficient universes, the ordinary prime,
field, and finite-extension instances, and the original standard derived categories.
No hypothesis or conclusion changes. `ReductionComputedBy` still asks invertibility
of exactly the specified counit at the same homotopy quotient of P. The statements in
`Challenge.lean` are untouched. Any target-meaning review reopened by this definition
edit should verify this definitional equality; there is no mathematical change.

The public import of `DerivedScalarExtensionRestrictionAdjunction` supplies the
normalized definition; the proof-only import of
`IntegralReductionTowerWellDefinedUnrestricted` supplies `unrestrictedTowerCounit_isIso`.
Both import directions were checked and introduce no cycle.

## Old

```lean
def reductionCounit (Y : Scheme.{t}) (n : ℕ) :=
  (unrestrictedIntegralReductionExistence l E Y n).choose_spec.choose_spec.choose_spec
    |>.choose_spec.2.2.choose_spec.choose
```

## New

```lean
def reductionCounit (Y : Scheme.{t}) (n : ℕ) :=
  scalarReductionCounit l E Y n
```

## Users

A read-only source import-graph scan found one downstream module. Searching that
closure for `ReductionComputedBy` and the qualified counit name found only this item.
The downstream module's qualified references use the section tower, representative,
localization, and sections APIs, whose definitions and signatures stay unchanged.
Its unchanged source compiled against the new sandbox module in 50.6 seconds. The
temporary consumer verification copy is not part of the delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointPullbackRepresentativeDiagram | V3 | Same counit; computation uses the existing canonical API. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Imports the item; does not reference the counit or predicate; no adaptation needed. |

## Status

landed 20261026T071352-L-3921395 2026-10-26 (merge of deliver/V3/Sheaf.Paper.PointPullbackRepresentativeDiagram)
