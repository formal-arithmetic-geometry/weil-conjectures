## Reason

Withdraw the legacy compactification upper-shriek API. Its proper-pushforward
left-adjoint assertion is false for proper pro-etale maps: the ambient abelian-variety
counterexample shows failure of coproduct preservation. The active finite-coefficient
exceptional inverse image is defined in `Derived.UpperShriek`.

## Old

The module declared the legacy `CompactificationUpperShriek` definitions and assumed
`isLeftAdjoint_rightDerivedLowerStar_of_isProper`.

## New

The module is retained as an importable empty module with a docstring marking the disputed
assertion. No declarations are exported.

## Users

The aggregate `WeilConjectures` index and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek` retain their
existing public imports; those imports remain valid because this path remains a module.

## Status

landed 20261016T221610-L-1615087 2026-10-16 (merge of deliver/F3/WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifUpperShriek)

Additional downstream users checked by preflight: `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral`,
`WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition`.
