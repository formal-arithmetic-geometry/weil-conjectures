# AlgebraicGeometry.ProEtale.integralConstantModelHeart

## Reason

The static interface check flags new scoped namespace opens used by the proof.
They enable the standard zero-object notation and the monoid-object instances of
pulled-back coefficient sheaves. The theorem statement, coefficient definition,
public imports, universes and declaration visibility are unchanged. No consumer
needs an adaptation.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

The public coefficient abbreviation was the canonical `Shrink`/spectral-norm
continuous coefficient ring, and the public theorem had its current signature
with proof `:= by sorry`.

## New

```lean
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject CategoryTheory.Obj
```

All added helpers are private and proved. They construct the continuous coefficient
isomorphism, transfer finite-presentation constructibility, assemble a weak Serre
heart, and normalize the spectral-norm instances before specializing to `Shrink`.
The theorem proof replaces its sole `sorry`. No existing public definition,
signature, attribute or import changes. The unit-route proof imports
`Sheaf.Paper.CartesianCoefficients` and `Sheaf.Paper.IntegralModels` are retained.

## Users

`tools/downstream.py Sheaf.Paper.IntegralConstantModelHeart --uses
integralConstantModelHeart` lists these ten downstream modules. No downstream
module textually mentions the theorem yet. All existing public declarations are
unchanged, so all consumers retain the same interface and require no adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralConstantModelHeart | Z8 | Private proof context and proof only; existing public interface unchanged. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | F5 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | H4 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Public signatures and definitions unchanged; no adaptation. |

## Status

landed 20261024T022611-L-3027441 2026-10-24 (merge of deliver/Z8/Sheaf.Paper.IntegralConstantModelHeart)
