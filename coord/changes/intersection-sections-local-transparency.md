# AlgebraicGeometry.Scheme.intersectionSheafMap: local transparency

## Reason

The complete proof uses local irreducibility to prevent repeated expansion of the
inverse-image sheaf and its inclusion. The new attributes are explicitly local to
IntersectionSectionsFlatBaseChange. All existing public definitions, theorem signatures,
visibility and public imports are preserved verbatim. No target meaning changes.
Preflight conservatively treats attribute commands as a visibility change and requires
this record. Only proof bodies, proved private helpers, private imports, and local
transparency commands change. The file compiles in 33.6 seconds.

## Old

The affected definitions have their original transparency and bodies:

```lean
def intersectionSheafMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type w} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) :
    intersectionStructureSheaf Y U ⟶
      (TopCat.Sheaf.pushforward CommRingCat (intersectionSubsetMap g U V h)).obj
        (intersectionStructureSheaf X V) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion Y U)).homEquiv _ _).symm
      ⟨g.c ≫ Functor.whiskerLeft (Opens.map g.base).op
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
          (intersectionInclusion X V)).unit.app X.sheaf).hom⟩

def intersectionStructureSheaf (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) :
    (TopCat.of {x : X // ∀ i : I, x ∈ U i}).Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat (intersectionInclusion X U)).obj X.sheaf

def intersectionInclusion (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) :
    TopCat.of {x : X // ∀ i : I, x ∈ U i} ⟶ X.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
```

## New

The definitions above remain verbatim. In the item module alone, the proof adds:

```lean
attribute [local irreducible] intersectionSheafMap
attribute [local irreducible] intersectionStructureSheaf intersectionInclusion
```

The first follows the unit-equation helper; the second follows the tensor-associator
helper. Declaration-scoped transparency options on private helpers do not export.
No downstream proof needs adaptation: these attributes expire at the end of the file.
The private QcOpenFlatSectionDiagram import supplies the stagewise comparison.

## Users

Computed with tools/downstream.py and checked named occurrences of intersectionSheafMap,
intersectionStructureSheaf, intersectionInclusion, intersectionSectionsMap and
intersectionBaseChangeMap. The following includes all 35 transitive downstream modules.
None sees the local attributes. Existing definitions and statement meanings are identical.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange` | D5 | Local proof elaboration only; 2 theorem holes closed. |
| `Sheaf.AlgebraicGeometry.AffineStackStabilizerEtaleComparison` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcValuativeDescent` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood` | J1 | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.CoproductFpqcEffectivity` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleAffineQuotientRepresentable` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleRelationQuotient` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse` | S9 | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.InvariantIntersectionAffineDescent` | C7 | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.InvariantOpenAffinizationEquivariance` | C8 | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperCurveAutomorphismScheme` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable` | W8 | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SeparatedLqfAffineRelationCover` | T2 | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SeparatedLqfFpqcDescent` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange` | unclaimed | No exported change; no adaptation. |
| `Sheaf.AlgebraicGeometry.UniverseEnlargedEtaleRealization` | unclaimed | No exported change; no adaptation. |
| `Sheaf.Paper.NormalLatticeFiniteCoverPresentation` | M6 | No exported change; no adaptation. |
| `Sheaf.Paper.NormalProEtaleMonodromy` | unclaimed | No exported change; no adaptation. |
| `Sheaf.Paper.StratifiedLatticeScheme` | unclaimed | No exported change; no adaptation. |
| `Sheaf.Paper.TameIntegralReductionFamily` | unclaimed | No exported change; no adaptation. |
| `Sheaf.SecPurity.NormalLocallyConstantFiniteSection` | S8 | No exported change; no adaptation. |
| `Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent` | unclaimed | No exported change; no adaptation. |

## Status

landed 20261023T131506-L-2113651 2026-10-23 (merge of deliver/D5/Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange)
