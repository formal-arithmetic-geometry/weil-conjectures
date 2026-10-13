# Change record: stalk K-flat tensor homology

## Reason

The proof requires proof-only imports and a local instance attribute for the
stalk tensor comparison, scalar restriction tensor comparison, exact stalk
homology, and derived K-flat model declarations.

## Old

The module had only its original public imports and contained a `sorry` proof.

## New

The module keeps all original public imports and adds private proof imports plus
`attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits`.
The theorem signature and declaration visibility are unchanged.

## Users

The module Sheaf.Algebra.Homology.StalkKFlatTensorHomology is held by H3.
Its downstream importers keep the same public interface and theorem signature.
The attribute is local and the imports are proof-only; no user needs adaptation.

## Status

landed 20261013T143545-L-560675 2026-10-13 (merge of deliver/H3/Sheaf.Algebra.Homology.StalkKFlatTensorHomology)
