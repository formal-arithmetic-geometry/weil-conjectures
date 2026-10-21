# AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose_factorization

## Reason

The returned restoration was already present in the current library. Repeating
it would be a no-op. This packet instead simplifies the actual categorical
proof of transpose_three_maps and removes the unnecessary theorem-local
backward.defeqAttrib.useBackward option. The public theorem uses this proved
helper, so its proof now rests on the shorter direct Mathlib calculation.

Reassociation and Adjunction.homEquiv_naturality_left_symm directly prove the
helper. The old explicit congrArg and equality transitivity are unnecessary.
The typed coefficientMate_evaluation helper remains: it keeps the counit and
base-change mate calculation away from expanded fibre-product expressions.
The defining coefficient equations and pinned adjunction remain unchanged.

No definition, statement, global attribute, public import or target meaning
changes. No time limit or heartbeat budget is increased. The shared derived
category parameter, universes, declaration visibility and docstrings stay
unchanged. No hole is added or removed.

## Old

```lean
private theorem transpose_three_maps
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {A B E : C} {N : D} (a : B ⟶ A) (ζ : A ⟶ E) (b : E ⟶ G.obj N) :
    (adj.homEquiv B N).symm (a ≫ ζ ≫ b) =
      F.map (a ≫ ζ) ≫ (adj.homEquiv E N).symm b := by
  exact (congrArg (adj.homEquiv B N).symm (Category.assoc a ζ b).symm).trans
    (adj.homEquiv_naturality_left_symm (a ≫ ζ) b)

```

The public theorem was also wrapped in:

```lean
set_option backward.defeqAttrib.useBackward true in
```

Its public statement is unchanged, verbatim:

```lean
theorem picardDirectImageDerivedTranspose_factorization
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {V : Scheme.{v}} (r : V ⟶ W)
    (ζ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) r) :
  let τ : ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
    picardCoefficientTranspose f L W k
  let e : ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback r).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings V.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings V.toRingedSpace)) :=
    picardDerivedUnitNormalization W
  picardDirectImageDerivedTranspose f L W k r ζ =
    (derivedPullback (pullback.snd f (r ≫ k))).map ((e r).inv ≫ ζ) ≫ τ r
```

## New

```lean
private theorem transpose_three_maps
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {A B E : C} {N : D} (a : B ⟶ A) (ζ : A ⟶ E) (b : E ⟶ G.obj N) :
    (adj.homEquiv B N).symm (a ≫ ζ ≫ b) =
      F.map (a ≫ ζ) ≫ (adj.homEquiv E N).symm b := by
  rw [← Category.assoc a ζ, adj.homEquiv_naturality_left_symm]

```

The theorem-local backward.defeqAttrib.useBackward wrapper is removed. All
other original elaboration settings and the public theorem's proof script
remain unchanged. The changed private helper supplies its direct Mathlib
naturality proof. The coefficient helper is retained with its complete proof.

The node is rebased on the current record; only proof, proof_deps and
proof_origin change. The inventory now includes the coefficient defining
equations and schemeDerivedMate_evaluation actually used by the proof. The
module-pullback adjunction remains a statement dependency of the coefficient
data but is not a direct proof dependency of this categorical calculation.
The unit route is preserved.

## Users

The current downstream.py --uses inventory has one live downstream module,
PicardDirectImageDerivedTransposePasting, which is the only theorem user and
DAG parent. Including quarantined sources gives the following 17 consumers.
Live sources take precedence over their archived versions. Every consumer sees
the identical public interface. No consumer is changed in the delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting | no local claim record | Direct importer and theorem user; signature unchanged, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | no local claim record | Quarantined transitive importer; same public interface, no adaptation. |

The revised module and its axiom probe compile cleanly. The unchanged direct
consumer reaches the 60-second limit against both the revised exported module
and the unchanged exported source control; report.md records this pre-existing
consumer timing issue. No interface adaptation is required. No source-library module is edited and no target
statement or target meaning changes.

## Status

landed 20261021T100941-L-4177378 2026-10-21 (merge of deliver/E4/Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization)
