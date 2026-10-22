# SheafOfModules.ScalarPullback.moduleComparison

## Reason

The delivery's combined compile/axiom check exceeded 60 seconds although the
standalone module compiled in 45.5 seconds. The existing composition and identity
proofs repeatedly unfolded the comparison constructor, including its linearity,
naturality and invertibility proofs, to calculate its underlying map or evaluate
it on sections. Add two proved private formulas for those operations and make
the constructor locally irreducible after the formulas are proved. Its definition
body, type and visibility remain unchanged. No check or time limit is changed.

The component formulas of `θ_composition` and `θ_identity`, and the underlying-map
calculation in their proofs, now use this API. Both theorem signatures and their
mathematical arguments remain unchanged. The local attribute has no effect on
importers. No public definition, attribute or target meaning changes.

## Old

```lean
set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits F]
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (γ : F ≅ G) (I : InverseImage F A B) (I' : InverseImage G A B)
    (hr : γ.hom.app _ ≫ (inverseRing I').hom = (inverseRing I).hom) :
    inverseModules I ≅ inverseModules I' := by
  let f (M : Modules A) : (inverseModules I).obj M ⟶ (inverseModules I').obj M :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          { toFun := ((CategoryTheory.moduleComparisonApp γ I I' M).hom.app U)
            map_add' := ((CategoryTheory.moduleComparisonApp γ I I' M).hom.app U).hom.map_add
            map_smul' := by
              intro r x
              have h := CategoryTheory.module_compare_smul γ.hom I I' M U r x
              have he : CategoryTheory.compareMap γ.hom I.ringUnderlying I'.ringUnderlying =
                  𝟙 _ := by
                dsimp [CategoryTheory.compareMap]
                rw [hr, Iso.inv_hom_id]
              rw [he] at h
              exact h }
        naturality := by
          intro U V g
          ext x
          exact CategoryTheory.congr_fun
            ((CategoryTheory.moduleComparisonApp γ I I' M).hom.naturality g) x } }
  have hf (M : Modules A) : (underlying B).map (f M) =
      I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
    exact CategoryTheory.moduleComparisonApp_underlying γ I I' M
  let β : inverseModules I ⟶ inverseModules I' :=
    { app := f
      naturality := by
        intro M N g
        apply (underlying B).map_injective
        rw [Functor.map_comp, Functor.map_comp, hf, hf]
        have h := (I.moduleUnderlying ≪≫
          Functor.isoWhiskerLeft (underlying A) γ ≪≫ I'.moduleUnderlying.symm).hom.naturality g
        simpa only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
          NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
          Functor.whiskerLeft_app, Functor.comp_map, Category.assoc] using h }
  have hi (M : Modules A) : IsIso (β.app M) := by
    have h : (underlying B).map (β.app M) =
        I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
      exact CategoryTheory.moduleComparisonApp_underlying γ I I' M
    have : IsIso ((underlying B).map (β.app M)) := by rw [h]; infer_instance
    exact isIso_of_reflects_iso _ (underlying B)
  exact NatIso.ofComponents (fun M ↦ asIso (β.app M)) (fun g ↦ β.naturality g)
```

## New

```lean
set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits F]
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (γ : F ≅ G) (I : InverseImage F A B) (I' : InverseImage G A B)
    (hr : γ.hom.app _ ≫ (inverseRing I').hom = (inverseRing I).hom) :
    inverseModules I ≅ inverseModules I' := by
  let f (M : Modules A) : (inverseModules I).obj M ⟶ (inverseModules I').obj M :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          { toFun := ((CategoryTheory.moduleComparisonApp γ I I' M).hom.app U)
            map_add' := ((CategoryTheory.moduleComparisonApp γ I I' M).hom.app U).hom.map_add
            map_smul' := by
              intro r x
              have h := CategoryTheory.module_compare_smul γ.hom I I' M U r x
              have he : CategoryTheory.compareMap γ.hom I.ringUnderlying I'.ringUnderlying =
                  𝟙 _ := by
                dsimp [CategoryTheory.compareMap]
                rw [hr, Iso.inv_hom_id]
              rw [he] at h
              exact h }
        naturality := by
          intro U V g
          ext x
          exact CategoryTheory.congr_fun
            ((CategoryTheory.moduleComparisonApp γ I I' M).hom.naturality g) x } }
  have hf (M : Modules A) : (underlying B).map (f M) =
      I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
    exact CategoryTheory.moduleComparisonApp_underlying γ I I' M
  let β : inverseModules I ⟶ inverseModules I' :=
    { app := f
      naturality := by
        intro M N g
        apply (underlying B).map_injective
        rw [Functor.map_comp, Functor.map_comp, hf, hf]
        have h := (I.moduleUnderlying ≪≫
          Functor.isoWhiskerLeft (underlying A) γ ≪≫ I'.moduleUnderlying.symm).hom.naturality g
        simpa only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
          NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
          Functor.whiskerLeft_app, Functor.comp_map, Category.assoc] using h }
  have hi (M : Modules A) : IsIso (β.app M) := by
    have h : (underlying B).map (β.app M) =
        I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
      exact CategoryTheory.moduleComparisonApp_underlying γ I I' M
    have : IsIso ((underlying B).map (β.app M)) := by rw [h]; infer_instance
    exact isIso_of_reflects_iso _ (underlying B)
  exact NatIso.ofComponents (fun M ↦ asIso (β.app M)) (fun g ↦ β.naturality g)

set_option backward.isDefEq.respectTransparency false in
private theorem moduleComparison_underlying
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits F]
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (γ : F ≅ G) (I : InverseImage F A B) (I' : InverseImage G A B)
    (hr : γ.hom.app _ ≫ (inverseRing I').hom = (inverseRing I).hom)
    (M : Modules A) :
    (underlying B).map ((moduleComparison γ I I' hr).hom.app M) =
      I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
  unfold moduleComparison
  exact CategoryTheory.moduleComparisonApp_underlying γ I I' M

set_option backward.isDefEq.respectTransparency false in
private theorem moduleComparison_hom_apply
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits F]
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (γ : F ≅ G) (I : InverseImage F A B) (I' : InverseImage G A B)
    (hr : γ.hom.app _ ≫ (inverseRing I').hom = (inverseRing I).hom)
    (M : Modules A) (U : Dᵒᵖ) (x : ((inverseModules I).obj M).val.obj U) :
    ((moduleComparison γ I I' hr).hom.app M).val.app U x =
      ((I'.moduleUnderlying.inv.app M).hom.app U
        ((γ.hom.app ((underlying A).obj M)).hom.app U
          ((I.moduleUnderlying.hom.app M).hom.app U (ULift.up x)))).down := by
  exact congrArg (fun q ↦ (q.hom.app U (ULift.up x)).down)
    (moduleComparison_underlying γ I I' hr M)

-- Use the comparison's underlying and section formulas without unfolding its proof fields.
attribute [local irreducible] moduleComparison
```

## Users

`python3 tools/downstream.py Sheaf.Paper.KFlatScalarComparisonNormalization
--uses moduleComparison` finds uses only inside the item module. Its eleven
transitive importers are listed below. Only proofs in the item module are
adapted; there are no external consumer changes.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | K3 | Private underlying/section API added; composition and identity proofs use it. |
| `Sheaf.Paper.ClosedSupportedScalarComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.ConstructibleAlgClTopologyComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.ContinuousAlgClOpenScalarComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.ProperIntegralRationalScalarComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | E9 | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.QcqsProperConstructibleClosedBaseChange` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.QuotientExpressionKFlatNormalization` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.SupportedFiniteStageTopologyDefect` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.TameBoundaryScalarComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed | No use of the private declaration; no adaptation or public interface change. |
| `Sheaf.SixFunctors.OpenScalarConjugateNormalization` | unclaimed | No use of the private declaration; no adaptation or public interface change. |

## Status

landed 20261022T020104-L-15317 2026-10-22 (merge of deliver/K3/Sheaf.Paper.KFlatScalarComparisonNormalization)
