# AlgebraicGeometry.ProEtale.CoefOpenCounit.coefficient_factored_aux

## Reason

The original target proof is decomposed into the finite coefficient-domain portion and the independent unbounded scalar/open mate calculation. This named public theorem records the first strict subclaim; the target theorem uses it to assemble its first two conjuncts.

## Old

No declaration existed in `Sheaf.SixFunctors.OpenScalarAdjunctionCounit`.

## New

A named theorem with the exact finite coefficient hypotheses and conclusion
`CoefficientFactored F.k l E m hm t j c ∧ CoefficientFactored F.k l L n hn t j c`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | D7 | The target theorem invokes the two projections; no external importer uses the helper. |

## Status

landed 20261027T233901-L-4131080 2026-10-27 (merge of deliver/D7/Sheaf.SixFunctors.OpenScalarAdjunctionCounit)

# AlgebraicGeometry.ProEtale.CoefOpenCounit.scalar_counit_aux

## Reason

The unbounded normalized scalar/open counit calculation is isolated as a strict lower statement in its own module, so the assigned theorem can combine it with the finite coefficient-domain package.

## Old

No declaration existed in `Sheaf.SixFunctors.OpenScalarAdjunctionCounitScalarAux`.

## New

A named theorem asserting the normalized scalar/open counit equation for every object of the unbounded derived category, with no coefficient-flatness hypothesis.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | D7 | The target theorem invokes it as the third conjunction component. |

## Status

landed 20261027T233901-L-4131080 2026-10-27 (merge of deliver/D7/Sheaf.SixFunctors.OpenScalarAdjunctionCounit)
