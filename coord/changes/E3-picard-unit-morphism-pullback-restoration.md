# AlgebraicGeometry.Scheme.picardDirectImageUnitMorphism_pullback

## Reason

Restore the assigned quarantined module from the path in coord/rework.tsv.
The live Lean module is absent; this is a cluster-restore rework, not a withdrawal.
Its preserved implementation has zero holes and remains required by the section
restriction theorem and the theorem-of-the-cube route.

The unmodified archive fails in its private singlePullback_naturality signature:
inside namespace AlgebraicGeometry.Scheme.Modules, derivedPullback now resolves
to the newer Scheme.Modules.derivedPullback. The compiler expects a Type v
morphism but canonicalSinglePullbackMap supplies a Type (v + 1) morphism for the
shared derived category. Qualify that one occurrence as
AlgebraicGeometry.derivedPullback, the functor already specified by the proof's
exists_schemeDerivedAdjunction and the canonical single-pullback comparisons.
The resulting module compiles cleanly in 44.5 seconds.

## Old

The live path lean/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphismPullback.lean
is absent. Its complete archived source is preserved at
quarantine/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphismPullback.lean.
The failing private helper begins:

```lean
private theorem singlePullback_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{v}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N) :
    (derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
      canonicalSinglePullbackMap f N =
    canonicalSinglePullbackMap f M ≫
      (DerivedCategory.singleFunctor _ 0).map ((pullback f).map a)
```

The archived public signature is:

```lean
theorem picardDirectImageUnitMorphism_pullback
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (h : i ≫ t = t')
        (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k)),
        ∀ (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k)),
          j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i →
          let c := (conjugateIsoEquiv
            ((Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t ≫ k)))).comp
                (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
            (Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t' ≫ k))))).symm
            (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
              Modules.pushforwardCongr hj₁)
          ∀ ξ : picardDerivedModelSections E t,
            let U := SheafOfModules.unit
              (moduleRings (pullback f (t ≫ k)).toRingedSpace)
            let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction j)
            (adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction j)).hom.app U ≫
                SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom ≫
                picardDirectImageUnitMorphism f L W k t'
                  (picardDerivedModelRestriction E i t t' h ξ) =
              (Modules.tensorPullback j).map
                (picardDirectImageUnitMorphism f L W k t ξ) ≫ (c.app L).inv
```

## New

Restore the full archived source and qualify the private helper's first functor:

```lean
private theorem singlePullback_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{v}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N) :
    (AlgebraicGeometry.derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
      canonicalSinglePullbackMap f N =
    canonicalSinglePullbackMap f M ≫
      (DerivedCategory.singleFunctor _ 0).map ((pullback f).map a)
```

The public signature above and its proof remain verbatim unchanged. Both existing
proofs, all imports, documentation, universes and local elaboration settings are
preserved. No new declaration, definition, axiom, proof hole or exported attribute
is introduced. The node changes only lean.by, lean.date and lean.note to describe
the restoration; its attachment, statement, proof dependencies and route remain.
The quarantine archive is untouched. No adopted-source file is changed.

## Users

The prescribed downstream.py query with --allow-missing reports zero current
users because the live item is absent. A source scan of lean/ and quarantine/,
with current live modules taking precedence, finds one direct importer and
15 transitive-or-direct consumers. They are listed below; none is adapted or
delivered. Local claim snapshots are not treated as a complete remote inventory.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction | no local claim record; separate rework | Direct importer and theorem user; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | no local claim record; separate rework | Transitive importer; identical restored public signature, no adaptation. |

The sole DAG parent is lem-sc-picard-direct-image-section-map-restriction.
Its proof still cites this node, whose statement and dependency attachment are
preserved. Restoring the theorem preserves every consumer's mathematical meaning;
no target signature or definition used in a target is changed.

A separate validation sandbox recompiles the restored item in 49.0 seconds and
its archived direct consumer PicardDirectImageSectionMapRestriction unchanged in
28.7 seconds. The latter accepts the existing invocation of this theorem without
any adaptation. An axiom-check module reports exactly propext, Classical.choice
and Quot.sound for picardDirectImageUnitMorphism_pullback (2.4 seconds). The
consumer and probe remain under scratch/consumer-check and are not delivered.

## Status

landed 20261021T143852-L-14430 2026-10-21 (merge of deliver/E3/Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback)
