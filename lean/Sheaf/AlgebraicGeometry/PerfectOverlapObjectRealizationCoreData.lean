/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram

/-! # Core object comparison data (without the final Hom pin).

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Geometric object comparisons and their natural compatibility with apex pullback.
The transition functors and their fixed conjugation formula are recorded explicitly;
the Hom pin will be derived from naturality, rather than included as a field.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data). -/
structure PerfectHomObjectRealizationCore
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (C : Set.Ici i → Type v) [∀ k, Category.{h} (C k)]
    (F : ∀ k, Bool → C k) (D : Type v') [Category.{h'} D]
    (O : Bool → D) (G : ∀ k, C k ⥤ D)
    (ψ : ∀ k b, (G k).obj (F k b) ≅ O b)
    (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i)) (objects : Bool → schemeDerivedCategory Y)
    (stageEquiv : ∀ k : Set.Ici i, C k ≌
      schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))))
    (apexEquiv : D ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    where
  stageObj : ∀ k b, (stageEquiv k).functor.obj (F k b) ≅
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj
      (objects b)
  apexObj : ∀ b, apexEquiv.functor.obj (O b) ≅
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj (objects b)

  transition : ∀ k : Set.Ici i,
    schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))) ⥤
      schemeDerivedCategory (pullback s (Spec.map (c.ι.app i)))
  baseComparison : ∀ k : Set.Ici i,
    derivedPullback (pullback.fst s (Spec.map (c.ι.app i))) ≅
      derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property)))) ⋙ transition k
  transition_pin : ∀ (k : Set.Ici i) (P Q : schemeDerivedCategory Y)
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj Q),
    perfectLimitMap R c s k.property f =
      (baseComparison k).hom.app P ≫ (transition k).map f ≫ (baseComparison k).inv.app Q
  comparison : ∀ k : Set.Ici i,
    G k ⋙ apexEquiv.functor ≅ (stageEquiv k).functor ⋙ transition k
  object_pin : ∀ (k : Set.Ici i) (b : Bool),
    apexEquiv.functor.map (ψ k b).hom ≫ (apexObj b).hom ≫
      (baseComparison k).hom.app (objects b) =
        (comparison k).hom.app (F k b) ≫ (transition k).map (stageObj k b).hom

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

/-- The object-comparison proposition for the fixed overlap scheme and pullback objects.
Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data). -/
@[irreducible] noncomputable def perfectOverlapObjectRealizationCoreStatement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : Prop :=
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    Nonempty (
      Σ data : (k : I) → (hjk : j ≤ k) →
        perfectOverlapComparisonDataType R c hc i Z t j hij hstage
          U V hcover hU hV A B hA hB E φU φV k hjk,
      let K := {k : I // j ≤ k}
      let C : K → Type (u + 1) := fun k ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        schemeDerivedCategory (U' ⊓ V').toScheme
      let F : (k : K) → Bool → C k := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let SU : schemeDerivedCategory U'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
        let SV : schemeDerivedCategory V'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
        if b then SV.obj B' else SU.obj A'
      let G : (k : K) → C k ⥤
          DerivedCategory (SheafOfModules.{u}
            ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
        (data k.val k.property).d.toDiagram.HW
      let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let d := (data k.val k.property).d
        let θU := (data k.val k.property).θU
        let θV := (data k.val k.property).θV
        match b with
        | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
        | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
      let stageEquiv : ∀ k : K, C k ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (R.map (homOfLE k.property)))) := fun k ↦
        let arrow : Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
        perfectOverlapStageEquivalence (baseChangeMap t arrow)
          (pullback.snd t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (R.map (homOfLE k.property))) (isPullback_baseChangeMap t arrow) U V
      let apexEquiv : DerivedCategory (SheafOfModules.{u}
          ((moduleRings X.toRingedSpace).over (P ⊓ Q))) ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (c.ι.app j))) :=
        let arrow : Over.mk (Spec.map (c.ι.app i)) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
        perfectOverlapApexEquivalence gj
          (pullback.snd t (Spec.map (c.ι.app i)))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (c.ι.app j)) (isPullback_baseChangeMap t arrow) U V
      PerfectHomObjectRealizationCore R c j C F _ (fun _ ↦ RW.obj E) G ψ
        (U ⊓ V).toScheme
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (fun b ↦ if b then
          (derivedPullback (Yj.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B
          else (derivedPullback (Yj.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A) stageEquiv apexEquiv)





/-- The prescribed overlap comparison data exists simultaneously at every stage.
For each later index, identify the inverse-image intersection with the cartesian
base change of `U ⊓ V`, pull back along this identification, and apply the inverse
open-site equivalence. Restriction and derived-pullback composition comparisons
provide the transport data and theta equations.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data-family).
-/
theorem perfect_overlap_object_realization_core_data_family
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} ((SheafOfModules.{u})
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens)
    (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (hV : IsCompact (V : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (φU : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ U)).obj A ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E)
    (φV : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ V)).obj B ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E) :
    Nonempty (Σ data : (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij hstage
        U V hcover hU hV A B hA hB E φU φV k hjk, Unit) := by
  sorry

/-- Given the stagewise comparison data, the canonical transition and object pins
are assembled into the core realization structure.  The transition is obtained by
conjugating the overlap pullback functor by the fixed stage and apex equivalences.
The counit-pinned derived-pullback composition comparison gives `baseComparison`
and `transition_pin`; its naturality gives `comparison`.  Expanding the prescribed
`ψ` and the theta equations cancels the site unit and counit and proves `object_pin`.
This is the cartesian composition calculation from Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-of-data).
-/
theorem perfect_overlap_object_realization_core_of_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} ((SheafOfModules.{u})
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k) :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    ∀ (data : (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij hstage
        U V hcover hU hV A B hA hB E φU φV k hjk),
    Nonempty (
      let K := {k : I // j ≤ k}
      let C : K → Type (u + 1) := fun k ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        schemeDerivedCategory (U' ⊓ V').toScheme
      let F : (k : K) → Bool → C k := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let SU : schemeDerivedCategory U'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
        let SV : schemeDerivedCategory V'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
        if b then SV.obj B' else SU.obj A'
      let G : (k : K) → C k ⥤
          DerivedCategory (SheafOfModules.{u}
            ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
        (data k.val k.property).d.toDiagram.HW
      let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let d := (data k.val k.property).d
        let θU := (data k.val k.property).θU
        let θV := (data k.val k.property).θV
        match b with
        | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
        | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
      let stageEquiv : ∀ k : K, C k ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (R.map (homOfLE k.property)))) := fun k ↦
        let arrow : Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
        perfectOverlapStageEquivalence (baseChangeMap t arrow)
          (pullback.snd t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (R.map (homOfLE k.property))) (isPullback_baseChangeMap t arrow) U V
      let apexEquiv : DerivedCategory (SheafOfModules.{u}
          ((moduleRings X.toRingedSpace).over (P ⊓ Q))) ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (c.ι.app j))) :=
        let arrow : Over.mk (Spec.map (c.ι.app i)) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
        perfectOverlapApexEquivalence gj
          (pullback.snd t (Spec.map (c.ι.app i)))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (c.ι.app j)) (isPullback_baseChangeMap t arrow) U V
      PerfectHomObjectRealizationCore R c j C F _ (fun _ ↦ RW.obj E) G ψ
        (U ⊓ V).toScheme
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (fun b ↦ if b then
          (derivedPullback (Yj.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B
          else (derivedPullback (Yj.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A)
        stageEquiv apexEquiv) := by
  sorry

set_option maxHeartbeats 8000000 in
-- The Hom-continuity packaging unfolds a large dependent proposition.
/-- Geometric natural comparison and pinned object comparisons.
Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).

Proof: Identify the inverse-image intersections with the base changes of U intersection V
by the universal property of pullbacks. Derive pullback along these scheme isomorphisms,
and compose the apex equivalence with the inverse open-site equivalence. The restriction
and composition isomorphisms give the stage object isomorphisms. Restrict phiU and phiV
and compose with the apex cartesian isomorphism to give the apex object isomorphisms.
Construct the comparison diagrams using these same pullbacks and open-site equivalences.
Set theta to kappa followed by the image of phi followed by site; both theta equations
are reflexive. The cartesian composition comparison gives the natural comparison.
Expanding psi and theta, the site unit/counit cancel. Restriction coherence cancels
gamma and tau. Associativity of the fixed counit-pinned comparison gives object_pin.
All constructions apply to empty and coincident opens as well as arbitrary objects.
-/
theorem perfect_overlap_object_realization_core_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : perfectOverlapObjectRealizationCoreStatement R c hc i Z t j hij hstage := by
  unfold perfectOverlapObjectRealizationCoreStatement
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV
  have hh := perfect_overlap_object_realization_core_data_family R c hc i Z t j hij hstage
  obtain ⟨data, _unit⟩ := hh U V hcover hU hV A B hA hB E φU φV
  exact ⟨⟨data, Classical.choice
    (perfect_overlap_object_realization_core_of_data R c hc i Z t j hij hstage
      U V hcover hU hV A B hA hB E φU φV data)⟩⟩

end AlgebraicGeometry
