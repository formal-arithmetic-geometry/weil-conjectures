# fourArrowIntegralCoefficients_comm and fourArrowFiniteCoefficients_comm

## Reason

The rectangle uses the coefficient-compatible ambient exchange. Prove its two
coefficient identifications from the already stated four-corner composition laws.
Sheaf.Paper.ProperBaseChangeFourArrows is unclaimed in the current claim records.
The two theorem proof bodies are filled; their signatures and all definitions,
global attributes, visibility, and imports stay identical. Local proof-instance
priorities are aligned with the geometric functors as described in
Q4-finite-rectangle-reduction-type.md. There is no mathematical interface change.

## Old

```lean
theorem fourArrowIntegralCoefficients_comm (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) :
    HEq (proEtaleRingCompositeCoefficients g' f (adicDatumRing Y d)
      (adicDatumRing X d) (adicDatumRing X' d)
      (fourCornerCoefficientIso f d) (fourCornerCoefficientIso g' d))
      (proEtaleRingCompositeCoefficients f' g (adicDatumRing Y d)
        (adicDatumRing Y' d) (adicDatumRing X' d)
        (fourCornerCoefficientIso g d) (fourCornerCoefficientIso f' d))
```

```lean
theorem fourArrowFiniteCoefficients_comm (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    HEq (proEtaleRingCompositeCoefficients g' f
      ((adicLisseRingSystem Y d.ideal).obj (op n))
      ((adicLisseRingSystem X d.ideal).obj (op n))
      ((adicLisseRingSystem X' d.ideal).obj (op n))
      (fourCornerFiniteIso f d n) (fourCornerFiniteIso g' d n))
      (proEtaleRingCompositeCoefficients f' g
        ((adicLisseRingSystem Y d.ideal).obj (op n))
        ((adicLisseRingSystem Y' d.ideal).obj (op n))
        ((adicLisseRingSystem X' d.ideal).obj (op n))
        (fourCornerFiniteIso g d n) (fourCornerFiniteIso f' d n))
```
## New

Exactly the same signatures. Each proof identifies composite coefficients with
the coefficient isomorphism of the composite using fourCornerCoefficientCoherence,
then transports that dependent isomorphism across sq.toCommSq.w. No new hypotheses.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperBaseChangeFourArrows | unclaimed | Two theorem bodies proved. |
| Sheaf.Paper.FiniteLevelRectangle | Q4 | Uses the unchanged identifications. |
| Sheaf.Paper.FiniteReductionPullbackCoherence | new, Q4 | Uses the unchanged identifications. |

The downstream.py --uses scans report only ProperBaseChangeFourArrows as a current
user of either name. All seven downstream modules retain identical interfaces:
CompletedProjectionCoherence, CompletedPullbackUnitTower, CompletedTowerCompatibility,
FiniteLevelRectangle, ProEtaleConstantReductionTower, QuotientCornerFrobeniusStructures,
and StrictTowerExchangeMateNormalization. No adaptation of any other holder is made.

## Status

landed 20261020T233213-L-905022 2026-10-20 (merge of deliver/Q4/Sheaf.Paper.FiniteLevelRectangle)
