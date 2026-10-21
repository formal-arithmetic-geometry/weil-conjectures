# AlgebraicGeometry.Scheme.picardDirectImageSectionMap

## Reason

Restore the missing module from the exact quarantine path in coord/rework.tsv.
The entry records the 2026-10-20 cluster-restore rollback, not a withdrawal.
The current lean/ tree lacks the file while the DAG attachment and 23 quarantined
importers still need it. Restoring the complete implementation is the assigned
repair; this is an addition to the live library, not a rebase or an empty module.

The quarantined implementation compiles unchanged against the current dependencies
in 20.8 seconds, without errors or warnings. No additional defect in its definition
was found. Preserve it verbatim instead of altering the specified canonical map.
The fibre-product lift, inverse mate, coefficient comparison, single pullback map,
base-change mate, degree-zero direct image, evaluation at 1, top restriction, and
both additive laws are all retained. The inverses used are already proved to be
invertible. No data is supplied by a new existence assertion.

## Old

The live path is absent. The preserved archive has the following signature, under
its unchanged shared derived-category parameter:

```lean
variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

def picardDirectImageSectionMap {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W) :
    picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t →+
      Γ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L, ⊤)
```

## New

Restore lean/Sheaf/AlgebraicGeometry/PicardDirectImageSectionMap.lean byte for byte
from quarantine/Sheaf/AlgebraicGeometry/PicardDirectImageSectionMap.lean. Its
signature is:

```lean
def picardDirectImageSectionMap {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W) :
    picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t →+
      Γ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L, ⊤)
```

The complete body, section parameter, declaration visibility, five public imports,
options, module layout and docstrings are identical to the preserved archive.
Only the node's Lean restoration metadata is updated. Mathematical statements,
proof dependencies and the unit route are unchanged. No target statement or target
interpretation changes.

## Users

The prescribed tools/downstream.py command reports unknown module because the live
file is missing. The fallback scan uses the union of all lean/ and quarantine/
Lean source files, with the live source taking precedence. It finds three direct
public importers and 23 transitive importers, listed below. All are quarantined
and remain separate rework assignments. The four textual users are the bijectivity,
restriction, naturality and unit-morphism-evaluation modules. Since the complete
source is identical to the archive, their use of the definition does not become
weaker, stronger or different, including consumers that unfold the definition.
No forced adaptation or additional restoration is included in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTranspose | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeSingle | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapBijective | separate quarantined rework; not adapted | Direct public importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction | separate quarantined rework; not adapted | Direct public importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | separate quarantined rework; not adapted | Declaration user; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphism | separate quarantined rework; not adapted | Direct public importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismEvaluation | separate quarantined rework; not adapted | Declaration user; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | separate quarantined rework; not adapted | Transitive importer; identical full definition and imports, no semantic or interface change. |

The independent delivery reader checks the restoration, source identity, consumer
inventory and retained DAG attachment. No adopted-source module is modified.

## Status

landed 20261021T021025-L-2693087 2026-10-21 (merge of deliver/N4/Sheaf.AlgebraicGeometry.PicardDirectImageSectionMap)
