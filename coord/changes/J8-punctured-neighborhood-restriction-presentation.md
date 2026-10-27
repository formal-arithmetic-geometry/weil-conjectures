# TopCat.puncturedNeighborhood_cohomology_class_lift

## Reason

The general spectral-limit class-lifting theorem can be applied after constructing the
punctured inverse limit and its restriction coefficients. Open-subspace cohomology must
also be compared with ambient object cohomology with its specified canonical map.

## Old

```lean
theorem puncturedNeighborhood_cohomology_class_lift
    {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (q : ℕ)
    (y : (puncturedNeighborhoodCohomologyCocone Z hZ A q).pt) :
    ∃ (N : (compactOpenNeighborhoods Z)ᵒᵖ)
      (x : (puncturedNeighborhoodCohomologyDiagram Z hZ A q).obj N),
      ((puncturedNeighborhoodCohomologyCocone Z hZ A q).ι.app N).hom x = y
```

Its proof was `sorry`. The six new modules did not exist.

## New

The existing signature is verbatim unchanged. Six new modules provide the explicit
geometry, the explicitly constructed restriction system, transport through its constant
coefficient colimit, and a smaller open-subspace cohomology comparison. Their declarations
and exact signatures are recorded in their six delivered node files. The two comparisons and stage-representation statement
are named public theorems with whole-proof sorries and complete proofs in words.
Repair of the d311479effe return: the inverse-limit adapter imports the existing
Sheaf.Topology.PuncturedNeighborhoodSpectralSystem, reuses its
TopCat.puncturedNeighborhoodIndex, and removes the duplicate declaration from our new
module and its node attachment. Directedness and the geometric limit theorems now reuse
that module's proved declarations. No existing definition, instance, attribute, or public
import changes. The new composition
isomorphism is constructed by leftAdjointUniq and marked irreducible to bound elaboration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.PuncturedNeighborhoodCohomologyClassLift | J8 | Complete assembly uses the new modules through proof imports. |
| Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit | unclaimed | Existing direct consumer; identical class-lifting statement, no adaptation. |
| Sheaf.Topology.PuncturedNeighborhoodLegOpenSubspaceComparison | new in this delivery | Uses the explicit inverse-image composition construction. |
| Sheaf.Topology.OpenSystemColimitCohomologyComparison | new in this delivery | Uses the explicit coefficient diagram and comparison isomorphisms. |
| Sheaf.Topology.PuncturedNeighborhoodInverseLimit | new in this delivery | Uses the common inclusion construction for stages and projections. |

All existing consumers see the same interface. There are no forced adaptations.

## Status

landed 20261025T163802-L-834892 2026-10-25 (merge of deliver/J8/Sheaf.Topology.PuncturedNeighborhoodCohomologyClassLift)
