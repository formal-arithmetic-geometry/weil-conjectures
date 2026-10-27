# Profinite.IntegralScalar coordinates and reduction definitions

## Reason

The three strictly smaller intermediate statements need the existing coordinate and
quotient constructions. Keeping those definitions in the theorem file would create
an import cycle. Move the definitions verbatim to a definition-only module and publicly
re-export them from the original module. This is a dependency separation for the proof,
not a split to avoid a compile-time limit. No statement or definition is weakened.

## Old

`Sheaf.Topology.ProfiniteIntegralScalarRealization` defined the following names in
`Profinite.IntegralScalar`: topology, constant, constantSection, constantMonObj,
constantIsCommMonObj, ring, ringMonObj, power, residue, transition, reduce, generator,
ConstantCoordinates, ContinuousCoordinates, ScalarComparison, Represents, compatible,
limitMap, TopologyStatement, kernelSections, kernelSequences, kernelLimitMap,
MorphismStatement and Statement. It then stated integral_scalar_realization.
All declaration signatures and bodies preceding the final theorem are recorded
verbatim in the new definitions module delivered with this packet.

## New

The same declarations, signatures, bodies, attributes, universes and namespace are in
`Sheaf.Topology.ProfiniteIntegralScalarDefinitions`. The original module has
`public import Sheaf.Topology.ProfiniteIntegralScalarDefinitions`, so importing it
continues to expose the same public API and inherited public imports. Its theorem
signature is unchanged:

```lean
theorem integral_scalar_realization (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Statement l E
```

The three new statements use the definition-only module. The final theorem imports
those statements privately and proves all finite-reduction and kernel calculations.

## Users

`tools/downstream.py` finds zero current downstream Lean modules and no current uses
outside the assigned module. The unfinished DAG parent continues to depend on the
same theorem and definitions, with unchanged mathematical meaning. No target signature
or target definition changes, and no source-library file is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.ProfiniteIntegralScalarRealization | S7 | Re-exports the moved definitions; theorem type unchanged. |
| Sheaf.Topology.ProfiniteIntegralScalarDefinitions | new in S7 | Definitions copied verbatim; no holes. |
| Sheaf.Topology.ProfiniteIntegralModuleTopology | new in S7 | Uses the quotient and limit definitions. |
| Sheaf.Topology.ProfiniteIntegralScalarComparison | new in S7 | Uses normalized scalar-comparison definitions. |
| Sheaf.Topology.ProfiniteUniversalSectionMorphism | new in S7 | Uses continuous coordinates and Represents. |

## Status

landed 20261025T164307-L-992819 2026-10-25 (merge of deliver/S7/Sheaf.Topology.ProfiniteIntegralScalarRealization)
