# quotientReduction

## Reason

Separate the existing ordinary reduction constructions from the existence theorem,
so its ordinary evaluation and constant K-flatness proof lemmas can import those
constructions without importing the theorem they help prove. This is a proof dependency
change, not a compile-time split. Every relocated declaration keeps its name, full
signature, universes, attributes, and body verbatim. No mathematical definition changes.
The original module publicly imports the new core and preserves all original public imports.

## Old

In lean/Sheaf/Paper/QuotientSystemFlatModels.lean:

```lean
def quotientReduction (S : ScalarData.{c, v, max c v r} (quotientRingMap.{c, v, r} J R B τ α hα)) :
    CochainComplex (Mod.{c, v, max c v r} J R) ℤ ⥤ CochainComplex (Systems.{c, v, max c v r} J B
      τ) ℤ :=
  (quotientConstant.{c, v, r} J R ⋙ S.model.E).mapHomologicalComplex (.up ℤ)

/-- The strict tensor system Z_T is the actual total tensor of the two strict reductions.
Source: Stacks 06YN, 07A4 (blueprint: lem-pur-quotient-system-flat-models). -/
def quotientTensor (S : ScalarData.{c, v, max c v r} (quotientRingMap.{c, v, r} J R B τ α hα)) :=
  ((quotientReduction.{c, v, r} J R B τ α hα S).prod
    (quotientReduction.{c, v, r} J R B τ α hα S)) ⋙
      totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
```

The preceding projection, constant-ring, constant-module and quotient-ring-map declarations
are in the same original module.

## New

In lean/Sheaf/Paper/QuotientReductionCore.lean, unchanged:

```lean
def quotientReduction (S : ScalarData.{c, v, max c v r} (quotientRingMap.{c, v, r} J R B τ α hα)) :
    CochainComplex (Mod.{c, v, max c v r} J R) ℤ ⥤ CochainComplex (Systems.{c, v, max c v r} J B
      τ) ℤ :=
  (quotientConstant.{c, v, r} J R ⋙ S.model.E).mapHomologicalComplex (.up ℤ)

/-- The strict tensor system Z_T is the actual total tensor of the two strict reductions.
Source: Stacks 06YN, 07A4 (blueprint: lem-pur-quotient-system-flat-models). -/
def quotientTensor (S : ScalarData.{c, v, max c v r} (quotientRingMap.{c, v, r} J R B τ α hα)) :=
  ((quotientReduction.{c, v, r} J R B τ α hα S).prod
    (quotientReduction.{c, v, r} J R B τ α hα S)) ⋙
      totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
```

The preceding projection, constant-ring, constant-module and quotient-ring-map declarations
move verbatim with these definitions. The original module adds
`public import Sheaf.Paper.QuotientReductionCore`, so existing imports still expose every name.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.MixedReductionUnitComposition | unclaimed in the shared claims snapshot | The uses of quotientConstantRing, quotientRingMap and quotientConstant resolve through the unchanged public interface; no adaptation. |
| Sheaf.Paper.QuotientSystemFlatModels | F2 | Publicly re-exports the moved definitions and proves the flat-model package from the new lower lemmas. |
| Sheaf.Paper.QuotientOrdinaryModels | F2 (new module) | Imports the core to state the ordinary slice comparison. |
| Sheaf.Paper.QuotientConstantKFlat | F2 (new module) | Imports the core to prove preservation under the constant functor. |

`tools/downstream.py Sheaf.Paper.QuotientSystemFlatModels --uses quotientConstant`
reported the one external downstream module above. Other project declarations with similar
unqualified names are in unrelated namespaces and do not consume these definitions.
The constant-definition DAG attachment follows its declarations to the core module;
the new core node owns the ordinary reduction definitions. The main node adds that
new owner to stmt_deps because these same definitions occur in its statement. The
mathematical statement is unchanged. All target meanings stay identical.

## Status

landed 20261026T023109-L-519959 2026-10-26 (merge of deliver/F2/Sheaf.Paper.QuotientSystemFlatModels)
