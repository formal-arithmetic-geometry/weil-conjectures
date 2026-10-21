# Rep.discreteContinuousRep_commGrp

## Reason

Retire the duplicate explicitly listed in coord/retire-items.tsv. The item has
zero holes, and its theorem docstring, signature and complete proof are
byte-identical to WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrp.
The upstream source is preserved verbatim.

The Sheaf file publicly imports EtaleFieldGsets and globally registers
AlgebraicGeometry.etaleFieldDiscreteForget₂ and
AlgebraicGeometry.etaleFieldActionForget₂. The twin imports
EtaleFieldGeometricAction and registers those instances locally. The sole direct
consumer already publicly imports EtaleFieldGsets and registers those two
instances globally itself. Its public API is therefore preserved by the import
migration; no additional instance or public import is needed.

## Old

In Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp:

```lean
theorem discreteContinuousRep_commGrp
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    let D := DiscreteContinuousRep.{0, u, w} ℤ G
    let U : D ⥤ Rep.{w} ℤ G := ObjectProperty.ι _
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
    ∃ E : CommGrp (DiscreteContAction (Type w) G) ≌ D,
      Nonempty (E.functor ⋙ U ⋙ RepToAction ℤ G ⋙
        (CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G ≅
          CommGrp.forget _ ⋙ V)
```

In the sole direct consumer:

```lean
import Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp
```

## New

Keep the identical declaration, signature and proved body at
WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrp. Withdraw the Sheaf
duplicate through deleted.txt and redirect the existing mathematical node's
Lean attachment to this twin, with existing:true. Change the consumer to:

```lean
import WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrp
```

No hypothesis, definition, conclusion, proof dependency or unit step changes.
The equivalence and natural action comparison are retained, for every carrier
universe and arbitrary Cartesian monoidal structure and braiding. The trivial
group, zero module and non-Hausdorff topological groups remain included.
No target statement or definition used in a target changes.

## Users

The complete downstream closure reported by tools/downstream.py has
17 modules. The sole direct importer and sole external textual user
of Rep.discreteContinuousRep_commGrp is the adapted consumer. All indirect
users retain the same public imports, instance registrations and declarations.
The DAG parents continue to use the same node and theorem; its attachment now
names the retained upstream module. The unit sk-prop-h2 has no realized node at
this level and its route is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModules | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesData | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesTransport | unclaimed | Replace the private proof import; retain all declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceRetraction | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | D9 | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | No edit; the direct consumer retains the same public API. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | No edit; the direct consumer retains the same public API. |

The adapted consumer compiled cleanly through lcompile.py on the project server
in 6.2 seconds, with no warnings. The replacement import is cycle-free.

## Status

landed 20261021T001153-L-1379738 2026-10-21 (merge of deliver/X2/Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp)
