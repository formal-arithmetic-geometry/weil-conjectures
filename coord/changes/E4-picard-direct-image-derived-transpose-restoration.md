# AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose

## Reason

Restore the complete definition from the exact quarantine path recorded in
coord/rework.tsv. The 2026-10-20 cluster-restore rollback removed the live module;
it did not withdraw the definition. Its DAG attachment and the three parent
nodes still require it. This repair restores actual canonical morphism data,
including the full original implementation, rather than an empty compatibility
module or a proof-hole replacement.

The original archived module compiles unchanged against the current interfaces
in 27.8 seconds, without warnings or errors. Its construction normalizes the
structure-sheaf source, composes canonical derived base change with the pinned
single-pullback map and the coefficient comparison, then applies the inverse Hom
equivalence of the pinned derived adjunction. No fibre-unit normalization or
homology functor is applied here. The ordinary and derived adjunction choices
have their canonical units or derived compatibility specified by their existing
theorems; no arbitrary witness of mere existence is introduced.

## Old

The live Lean path is absent. The complete definition is preserved at
quarantine/Sheaf/AlgebraicGeometry/PicardDirectImageDerivedTranspose.lean.
Its signature, under the original shared derived-category parameter, is:

```lean
variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

def picardDirectImageDerivedTranspose {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    (derivedPullback (pullback.snd f (t ≫ k))).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings T.toRingedSpace))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L)
```

## New

Restore the original module byte for byte, including its shared derived-category
parameter, universes, public import of PicardDirectImageUnitMorphism,
irreducibility attribute, elaboration options, documentation and full body:

```lean
@[irreducible]
def picardDirectImageDerivedTranspose {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    (derivedPullback (pullback.snd f (t ≫ k))).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings T.toRingedSpace))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let M := (Modules.tensorPullback (pullback.fst f k)).obj L
  let N := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
  let a : pullback f (t ≫ k) ⟶ pullback f k :=
    pullback.lift (pullback.fst f (t ≫ k)) (pullback.snd f (t ≫ k) ≫ t)
      (by rw [Category.assoc]; exact pullback.condition)
  have ha : a ≫ pullback.fst f k = pullback.fst f (t ≫ k) := pullback.lift_fst ..
  have hb : a ≫ pullback.snd f k = pullback.snd f (t ≫ k) ≫ t := pullback.lift_snd ..
  let c := (conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).comp
      (Classical.choose (Modules.exists_tensorPullbackAdjunction a)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (t ≫ k))))).symm
    (Modules.pushforwardComp a (pullback.fst f k) ≪≫ Modules.pushforwardCongr ha)
  let d : (Modules.pullback a).obj M ≅ N :=
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction a)).symm.app M ≪≫ (c.app L).symm
  let B := schemeDerivedBaseChangeMap (pullback.snd f k) (pullback.snd f (t ≫ k))
    t a hb ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (schemeDerivedDirectImage (pullback.snd f (t ≫ k))).map
        (Modules.canonicalSinglePullbackMap a M ≫
          (DerivedCategory.singleFunctor _ 0).map d.hom)
  let U := SheafOfModules.unit (moduleRings W.toRingedSpace)
  have hU : SheafOfModules.IsInvertible.{v, v, v} U := by
    dsimp [U]
    exact SheafOfModules.instIsInvertibleUnit.{v, v, v}
  letI := hU
  have : IsIso (Modules.canonicalSinglePullbackMap t U) :=
    Modules.isIso_canonicalSinglePullbackMap t U
  let e := asIso (Modules.canonicalSinglePullbackMap t U) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit t.toRingCatSheafHom))
  let p := pullback.snd f (t ≫ k)
  let adj := Classical.choose (exists_schemeDerivedAdjunction p
    (hAdd := (Classical.choose exists_derivedPullbackComposition) p)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) p)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) p))
  exact (adj.homEquiv _ _).symm (e.inv ≫ ξ ≫ B)

```

Only the node's Lean restoration metadata changes. Its declaration attachment,
statement, statement dependencies, empty proof dependency list, source and unit
route are preserved. There is no target-signature or target-meaning change.

## Users

The prescribed downstream command with --allow-missing and --uses reports zero
live consumers because this module and its consumers are quarantined. A scan of
both lean/ and quarantine/ with live sources taking precedence finds three
direct importers (also the only declaration users) and 19 transitive consumers.
The complete inventory follows; no consumer is changed by this restoration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization | separate quarantined rework; no local claim snapshot | Direct importer and declaration user; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting | separate quarantined rework; no local claim snapshot | Direct importer and declaration user; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeSingle | separate quarantined rework; no local claim snapshot | Direct importer and declaration user; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | separate quarantined rework; no local claim snapshot | Transitive importer; identical restored implementation, no adaptation. |

The parent nodes are lem-sc-picard-direct-image-derived-transpose-single,
lem-sc-picard-direct-image-derived-transpose-factorization and
lem-sc-picard-direct-image-derived-transpose-pasting. Their dependencies remain
attached, including while their own Lean modules await separate restoration.
Existing signatures and explicit constructions have exactly their archived
meaning. The source library is not modified.

The archived direct consumer proofs were compiled unchanged in a separate scratch
sandbox against this exact restored file: factorization in 25.8 seconds, the
single-module comparison in 48.0 seconds and pasting in 37.7 seconds. The restored
module was also recompiled in 26.7 seconds in that set. Each file is below the
60-second limit. These consumer checks include unfolding the restored definition;
no consumer source adaptation is necessary or included in the delivery.

## Status

landed 20261021T023306-L-2945254 2026-10-21 (merge of deliver/E4/Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTranspose)
