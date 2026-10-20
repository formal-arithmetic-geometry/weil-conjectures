## Reason

The proof of the existing `restriction_properties` declaration needs the ordinary coefficient
adjunction implementation from `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`.
A proof-only import is required to expose that implementation to this module.

## Old

The module did not import `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`.
The declaration used only the public import closure.

## New

The module imports `all Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`.
The import is used only by proofs; no public declaration signature or definition is changed.

## Users

External users see the same declarations and signatures. The import adds proof dependencies only;
private helper declarations remain private.

## Status

landed 20261020T230754-L-611141 2026-10-20 (merge of deliver/J4/Sheaf.Paper.ConstantRealizationDerivedScalarExtension)
