# Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGenerator

## Reason

The assigned theorem now imports a proof-only integral-generator module and
therefore exposes that module and its named theorem to downstream proof users.

## New

Added `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherenceGeneratorIntegral`,
which isolates the finite-Tor numerator calculation. The assigned theorem's
signature is unchanged; its proof constructs the integral representative and
applies the new theorem.

## Users

The direct importer `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence` is
compiled against this delivery by `deliver3.py`.
