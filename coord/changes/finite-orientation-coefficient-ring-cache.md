# AlgebraicGeometry.ProEtale.SpFiniteOrientation.towerCoefficientCommRing

## Reason

The two uniformizer comparison signatures use the concrete lifted ell-power quotient
ring. Reconstructing its commutative-ring instance repeatedly made Lean's exported
symbol-frequency and Sine Qua Non indices spend approximately 22 seconds each on
these signatures. Export exceeded the 60-second per-file limit although ordinary
elaboration and kernel checking finished within that limit. A named cache of the
existing structure reduces the measured signature-indexing pass to approximately
4 seconds. It also reduces elaboration of the existing purity comparison proof.
This is a definition cache, not a change to coefficient rings or their operations.
No export extension, kernel check, heartbeat limit or compile limit is disabled.

## Old

There was no named cache to replace. The existing coefficient type appearing in
both uniformizer comparison signatures is, verbatim:

```lean
ULift.{u + 1} (SpTowerShriek.R P.coefficients.l P.extension n)
```

Typeclass synthesis supplied its ordinary lifted quotient-ring structure directly.
Every existing declaration's statement text and every existing definition body is
retained verbatim; the inferred ring dictionary is definitionally the same.

## New

```lean
@[instance_reducible]
def towerCoefficientCommRing (P : PurityFiniteSetting.{u}) (n : ℕ) :
    CommRing (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l P.extension n)) :=
  inferInstance

attribute [local instance] towerCoefficientCommRing
```

The named structure is constructed directly by ordinary typeclass synthesis,
before its local instance registration. It contains no postponed proof or choice
of new data. The local registration lets subsequent declarations reuse this
public, definitionally equal structure without exporting an additional global
instance. The theorem statements retain their coefficients and hypotheses.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteOrientationReduction | E3 | The two uniformizer comparison signatures reuse the named quotient-ring dictionary; all existing statements and proofs except the assigned unit-reduction proof are preserved. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Sole downstream importer; its only use is unit_tower_mem, whose statement is unchanged. It uses neither uniformizer comparison; no adaptation is necessary. |

The consumer list was checked with tools/downstream.py for each of
uniformizer_orientation_agreement and uniformizer_purity_agreement, and by
reading the downstream importer's use of unit_tower_mem. Both comparison
names occur only in the item module. No target declaration changes.

## Status

landed 20261026T023051-L-517874 2026-10-26 (merge of deliver/E3/Sheaf.Paper.FiniteOrientationReduction)
