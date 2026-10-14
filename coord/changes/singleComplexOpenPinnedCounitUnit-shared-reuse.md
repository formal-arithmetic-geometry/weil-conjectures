# AlgebraicGeometry.singleComplexOpen_pinned_counit_unit

## Reason

Repair X-734c6 G1/C5 (packet §7): the unit-square delivery duplicated the private
counit_factorization and pinned_counit_unit calculations already proved by
SingleComplexOpenCounitCompatibility. Extract their implementation once into a
common lower dependency, SingleComplexOpenPinnedCounitUnit. Both callers import
it for proofs only. This is the explicitly requested duplicate-removal refactor,
not a compiler-forced adaptation or a split to evade the time limit.

Repair X-32f96 G1 (head 32f960ff3): obtained the normal S3 claim for
`Sheaf.AlgebraicGeometry.SingleComplexOpenCounitCompatibility` on 2026-10-14
at 09:11:03 UTC and verified its holder on the project server before updating
this record. The repository original compiles against the delivery artifacts,
so this refactor uses that claim and does not invoke forced adaptation.
The delivered Lean edits are preserved.

Repair of the returned delivery X-a4997 G1: acquired a fresh normal S3 claim
for `Sheaf.AlgebraicGeometry.SingleComplexOpenCounitCompatibility` at
2026-10-14 12:17:44 UTC and verified the live server claim at 12:18:05 UTC.
That earlier claim is historical; the fresh second-reading registry check below
records the current unclaimed state and supersedes the earlier ownership metadata.

## Old

The compatibility module contained these private declarations, duplicated by the
returned unit-square module:

```lean
private theorem counit_factorization
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₁} {L : D₁ ⥤ D₂} {R : D₂ ⥤ D₁}
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (b : G ⊣ H) (a : L ⊣ R)
    (ε : Q₁ ⋙ L ⟶ G ⋙ Q₂) (η : H ⋙ Q₁ ⟶ Q₂ ⋙ R)
    (h : ∀ (M : C₁) (K : C₂) (v : G.obj M ⟶ K),
      a.homEquiv (Q₁.obj M) (Q₂.obj K) (ε.app M ≫ Q₂.map v) =
        Q₁.map (b.homEquiv M K v) ≫ η.app K) (I : C₂) :
    L.map (η.app I) ≫ a.counit.app (Q₂.obj I) =
      ε.app (H.obj I) ≫ Q₂.map (b.counit.app I) := by
  apply (a.homEquiv (Q₁.obj (H.obj I)) (Q₂.obj I)).injective
  have h₁ := (a.homEquiv (Q₁.obj (H.obj I)) (Q₂.obj I)).apply_symm_apply (η.app I)
  have h₂ := (b.homEquiv (H.obj I) I).apply_symm_apply (𝟙 (H.obj I))
  simp only [a.homEquiv_counit] at h₁
  simp only [b.homEquiv_symm_id] at h₂
  rw [h₁, h, h₂, Q₁.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Elaborating the pinned derived functor data requires additional heartbeats.
private theorem pinned_counit_unit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ := (Classical.choose exists_derivedPullbackComposition) f
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback f).map (F.rightDerivedFunctorUnit.app I) ≫
        (a f).counit.app (DerivedCategory.Qh.obj I) =
      (ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
        DerivedCategory.Qh.map
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
            |>.mapHomotopyCategory (.up ℤ)).counit.app I) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have : (Scheme.Modules.tensorPullback f).Additive :=
    (Classical.choose exists_derivedPullbackComposition) f
  exact counit_factorization
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
      |>.mapHomotopyCategory (.up ℤ))
    (singleComplexOpenPinnedAdjunction f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit
    (Classical.choose_spec (exists_schemeDerivedAdjunction f
      (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f))) I

```

## New

The new shared module contains the same proved private generic calculation and
exports the pinned specialization with the following signature:

```lean
theorem singleComplexOpen_pinned_counit_unit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ := (Classical.choose exists_derivedPullbackComposition) f
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback f).map (F.rightDerivedFunctorUnit.app I) ≫
        (a f).counit.app (DerivedCategory.Qh.obj I) =
      (ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
        DerivedCategory.Qh.map
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
            |>.mapHomotopyCategory (.up ℤ)).counit.app I)
```

Both modules add the proof-only import
`Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedCounitUnit`. The unit-square
module removes both duplicate helpers and uses
`have hc := singleComplexOpen_pinned_counit_unit f I`. Compatibility removes its
old private implementations and applies the same shared theorem inside its
existing reassociated counit rewrite. All existing PUBLIC signatures and
visibility, public imports, definitions and docstrings are identical. The two
private implementations are moved, not duplicated. No target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedCounitUnit | new, S3 | Sole shared counit calculation; proved, no hole. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization | S3 | Remove both duplicate declarations; apply shared normalization. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCounitCompatibility | unclaimed | Reviewer-requested refactor of private helpers and their sole use; both existing public declarations are unchanged. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization | unclaimed | Existing unit-square signature and exported imports retained; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCube | unclaimed | Compatibility's public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation | unclaimed | Compatibility's public interface unchanged; no adaptation. |

No other source module used either private helper. The new dependency imports
only SingleComplexOpenPinnedAdjunction, so it sits below both callers and creates
no import cycle. Every changed file compiles below the unchanged 60-second limit.
The combined delivery overlay passes import_prune_check.py for all three
modules, including the new shared theorem and both changed callers.

Second-reading ownership check (2026-10-14 12:38:09 UTC): queried the live
server claim files without acquiring or renewing claims. Compatibility is
unclaimed; the unit-square item remains held by S3. This supersedes the earlier
reported acquisitions and retention. The Users table records compatibility as
unclaimed. The current delivery rule permits changes to an unclaimed module
(`deliver3.py` forced_adaptations and the stage-3 preflight ownership rule).
The original compatibility file compiles against the delivery artifacts, so
this remains a reviewer-requested refactor of an unclaimed module, with no
compiler-forced adaptation alleged. Existing public interfaces remain unchanged.

## Status

landed 20261014T130427-L-3287621 2026-10-14 (merge of deliver/S3/Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization)
