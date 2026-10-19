# AlgebraicGeometry.Etale.isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf

## Reason

The completed proof uses monoidal notation and the sheaf monoidal instance. The static gate
classifies its added open and local attribute commands as an interface change. All existing
public signatures, visibility and public imports stay identical. These commands only support
elaboration inside this module; the module system does not export proof-only imports.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
```

There was no local monoidal instance attribute or declaration-local unused-variable option.
The theorem signature itself is unchanged verbatim.

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
open AlgebraicGeometry TopologicalSpace
attribute [local instance] Sheaf.monoidalCategory
```

The theorem also has `set_option linter.unusedVariables false in`: its original coefficient
hypotheses are retained even though the proof only uses finiteness of the coefficients.
All additional helper declarations are private. No target definition or statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | G3 | No adaptation: its imported theorem has the identical signature and visibility. |

This is the sole direct importer found by searching both library roots. Since there is no
public signature or definition change, all further consumers keep the same theorem interface.

## Status

landed 20261019T034254-L-416121 2026-10-19 (merge of deliver/D5/Sheaf.Paper.PurEtaleLisseStratumCompact)
