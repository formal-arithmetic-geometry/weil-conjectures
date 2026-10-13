# Sheaf.Paper.ModuleCupNaiveDerivedCompatibility imports

## Reason

The unbounded compatibility statement uses module global sections and tensor
sections, but none of the nonnegative acyclic resolution structures. Replace
its public resolution-data import with the two imports providing its statement.
All existing declaration signatures stay unchanged. The definitionally identical
comparison-body refactor is recorded separately in module-cup-global-comparison.md.

## Old

```lean
public import Sheaf.Paper.ModuleCupResolutionData
```

## New

```lean
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
```

The comparison construction additionally publicly imports
Sheaf.Paper.ModuleCupKInjectiveTarget; the separate comparison change record
explains why this import is needed by its definition.
Local irreducibility attributes prevent unfolding the right-derived functor and
naive map while manipulating the diagram. These do not change any definition.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupNaiveDerivedCompatibility | G4 | Proof and imports changed; signatures preserved; the definitionally identical comparison refactor is recorded separately. |
| Sheaf.Paper.ModuleCupEqualDerivedMapsClass | unchanged, no adaptation | Its public import of ModuleCupResolutionRealization independently supplies resolution data. |

ModuleCupEqualDerivedMapsClass is the current direct importer. No downstream
statement changes meaning, and there are no forced adaptations. The five
Challenge declarations are untouched.

## Status

landed 20261013T153500-L-1085119 2026-10-13 (merge of deliver/G4/Sheaf.Paper.ModuleCupNaiveDerivedCompatibility)
