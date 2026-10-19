# Constant realization ordinary comparison proof scope

## Reason

The stage-3 proof of `Sheaf.Paper.ConstantRealizationDerivedScalarExtension` adds
private commuting-square helpers and local irreducibility attributes. The static
preflight classifies these commands as changes to the module environment because
it conservatively treats section variables, `set_option backward.isDefEq...`, and
local attributes as visible commands. They are proof-scoped implementation details;
public theorem signatures, definitions, and public imports remain unchanged.

## Old

The module contained `sorry` proofs of
`CategoryTheory.ConstantScalarRealization.restrictionIso_existsUnique` and
`CategoryTheory.ConstantScalarRealization.moduleComparison_tensor`, with only the
original module-level proof options and no private restriction/sheafification
construction.

## New

The module contains a proved `RestrictionSheafification` section, private local
scalar-lift helpers, and proof-scoped `set_option backward.isDefEq.respectTransparency`
and `attribute [local irreducible]` commands. The two existing theorem signatures
are byte-for-byte unchanged. The ordinary comparison proofs use only these helpers;
no public declaration or definition is changed.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.ConstantRealizationDerivedScalarExtension` | D5 | contains the proof-scoped helpers and is adapted in this delivery |
| downstream importers | various | no adaptation: private helpers and local attributes are not exported |

## Status

landed 20261019T231108-L-547596 2026-10-19 (merge of deliver/D5/Sheaf.Paper.ConstantRealizationDerivedScalarExtension)
