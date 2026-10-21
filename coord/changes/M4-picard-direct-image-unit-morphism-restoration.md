# AlgebraicGeometry.Scheme.picardDirectImageUnitMorphism

## Reason

Restore the missing implementation from the exact quarantine path in coord/rework.tsv.
The row records the 2026-10-20 cluster-restore rollback, rather than a withdrawal.
The live Lean path is absent, while its DAG attachment, four DAG consumers and
21 downstream archived modules still require it. Restoring the complete definition
is the assigned repair, and adds its actual canonical construction back to the library.

The archived implementation compiles unchanged against the current published
interfaces in 10.3 seconds with no warnings or errors. A separate consumer check
recompiled the same definition in 9.6 seconds and compiled the archived evaluation
proof unchanged in 12.0 seconds. Its proof unfolds this definition and cancels the
ordinary adjunction and the invertible structure-sheaf comparison, so this also
checks the definition against the already specified section map.

The construction first forms the fibre-product lift and the inverse mate identifying
its pulled-back coefficient with L_T. It then composes the canonical derived
base-change map, single pullback comparison and coefficient isomorphism; takes
H^0 and the canonical direct-image H^0 isomorphism; and transposes the resulting
O_T -> p_*L_T morphism. Precomposition by the inverse structure-sheaf comparison
gives O_(X_T) -> L_T. Every part of this explicit data is preserved. The existing
adjunction theorem is proved, with its unit pinned to the canonical sectionwise
formula; no arbitrary existence witness or new axiom supplies data.

## Old

The live path lean/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphism.lean is
absent. The preserved implementation is at
quarantine/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphism.lean, with the
following signature under its shared derived-category parameter:

```lean
variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

def picardDirectImageUnitMorphism {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    SheafOfModules.unit (moduleRings (pullback f (t ≫ k)).toRingedSpace) ⟶
      (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
```

## New

Restore lean/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphism.lean byte for
byte from the recorded quarantine archive. Its signature is:

```lean
def picardDirectImageUnitMorphism {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    SheafOfModules.unit (moduleRings (pullback f (t ≫ k)).toRingedSpace) ⟶
      (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
```

The full body, universe and shared derived-category parameter, public import,
visibility, module header, documentation and all elaboration options are identical
to the preserved implementation. Only the node's Lean restoration metadata changes.
Its declaration attachment, statement dependencies, empty proof dependency list and
unit route are preserved. No adopted source module is modified, and no target
statement or definition meaning changes.

## Users

The prescribed tools/downstream.py command was run with --allow-missing and --uses.
Since the live module is absent, an additional source scan includes both the live
lean/ roots and the quarantined roots, with live files taking precedence. It finds
three direct public importers and 21 transitive importers, all separate quarantined
rework items. Their complete inventory follows. The groups currently working on
other rework items are not inferred from the absence of local claim snapshots;
none of those modules is changed in this delivery.

Four nodes cite the restored definition in their statement or proof dependencies:
lem-sc-picard-direct-image-unit-morphism-evaluation,
lem-sc-picard-direct-image-unit-morphism-pullback,
lem-sc-picard-direct-image-derived-transpose-single and
def-sc-picard-direct-image-derived-transpose. All dependencies remain attached.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTranspose | separate quarantined rework; not adapted | Direct public importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeSingle | separate quarantined rework; not adapted | Transitive importer and declaration user; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction | separate quarantined rework; not adapted | Transitive importer and declaration user; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismEvaluation | separate quarantined rework; not adapted | Direct public importer and declaration user; identical full definition and interface, no adaptation needed. Its archived proof compiles unchanged against this restoration (12.0 s). |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback | separate quarantined rework; not adapted | Direct public importer and declaration user; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | separate quarantined rework; not adapted | Transitive importer; identical full definition and interface, no adaptation needed. |

The unchanged full source preserves the mathematical statements of all these
consumers, including proofs that unfold the definition. The independent delivery
reader can verify source identity, the retained DAG attachment and the consumer
inventory. No forced adaptation is included.

## Status

landed 20261021T021919-L-2792384 2026-10-21 (merge of deliver/M4/Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphism)
