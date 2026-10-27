# AlgebraicGeometry.AlgebraicSpace.universal_locally_surjective

## Reason

Repair the return at 38b16b42f: the neighbourhood proof duplicated this existing
private theorem. Expose the original theorem and reuse it through the existing
proof import. The dependency module is unclaimed. The theorem type and proof,
all geometric statements, and all public imports remain unchanged. No target
statement or definition changes.

## Old

```lean
private theorem universal_locally_surjective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type u) (F : Sheaf J (Type u)) (η : P ⟶ F.obj)
    (hη : ∀ G : Sheaf J (Type u),
      Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k)) :
    Presheaf.IsLocallySurjective J η
```

## New

```lean
theorem universal_locally_surjective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type u) (F : Sheaf J (Type u)) (η : P ⟶ F.obj)
    (hη : ∀ G : Sheaf J (Type u),
      Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k)) :
    Presheaf.IsLocallySurjective J η
```

## Users

The source search and `tools/downstream.py Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens
--uses universal_locally_surjective` find only the original module using the name
before this repair. Its two existing calls are unchanged. The complete transitive
consumer list follows; adding the public theorem requires no consumer adaptations.
The neighbourhood module already imports this module privately.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens` | unclaimed | Expose the existing helper; type and proof unchanged. |
| `Sheaf.AlgebraicGeometry.AffineStackStabilizerEtaleComparison` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceConstructibleAffineEtaleTest` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcQCSeparatedDescent` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceHigherDirectImageQuasiCoherent` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood` | J1 | Replace duplicate helper call with the existing theorem. |
| `Sheaf.AlgebraicGeometry.CurveSmoothPolarizationCover` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.EtaleQuotientAffineOpenCover` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.EtaleRelationQuotient` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.IntegralSpaceFinitePresentationLimit` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.ProperCurveAutomorphismScheme` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.ReducedSingletonFieldFactorization` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.RepresentableLocallyQuasiFiniteCalculus` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SeparatedGroupSpaceGeometricScheme` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SeparatedLqfAffineRelationCover` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SpaceEtalePullPushRetract` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SpacePerfectUniformTor` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SpaceSquareZeroRingedRealization` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SpaceSupportedPerfectApproximation` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.SubtrusiveTopologicalDescentCalculus` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.AlgebraicGeometry.UniverseEnlargedEtaleRealization` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.Paper.NormalLatticeFiniteCoverPresentation` | M6 | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.Paper.NormalProEtaleMonodromy` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.Paper.TameIntegralReductionFamily` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |
| `Sheaf.SecPurity.NormalLocallyConstantFiniteSection` | unclaimed | No adaptation: the added public name has no occurrences in this consumer. |

## Status

landed 20261024T190038-L-3878668 2026-10-24 (merge of deliver/J1/Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood)
