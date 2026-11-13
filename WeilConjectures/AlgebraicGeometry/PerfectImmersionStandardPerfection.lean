/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardCokernel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Perfection of closed-immersion pushforward in the standard localization

## References

* Stacks Project, Tags 05RU, 08CM and 0A9U.
-/

@[expose] public section

set_option autoImplicit false

universe u wY

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Isomorphisms between localized complexes transport to the standard localization. -/
private noncomputable def standardComplexIso
    {C : Type*} [Category C] [Abelian C] [h : HasDerivedCategory.{wY} C]
    {K L : CochainComplex C ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard _)).obj K ≅
      (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard _)).obj L := by
  let Q := @DerivedCategory.Q C _ _ h
  let Q' := @DerivedCategory.Q C _ _ (HasDerivedCategory.standard _)
  let W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  let E := Localization.uniq Q Q' W
  let c := Localization.compUniqFunctor Q Q' W
  exact (c.app K).symm ≪≫ E.functor.mapIso e ≪≫ c.app L

/-- Transport the same local strictly perfect witnesses for a single module. -/
private theorem standardSinglePerfect (Y : Scheme.{u})
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (h : Y.IsPerfect ((DerivedCategory.singleFunctor _ 0).obj M)) :
    @Scheme.IsPerfect Y (HasDerivedCategory.standard _)
      (fun _ ↦ HasDerivedCategory.standard _)
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj M) := by
  intro x
  obtain ⟨U, hx, K, hK, ⟨e⟩⟩ := h x
  refine ⟨U, hx, K, hK, ?_⟩
  let F := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U
  let c := (F.mapDerivedCategorySingleFunctor 0).app M
  let d := (DerivedCategory.singleFunctorIsoCompQ _ 0).app (F.obj M)
  let e' := standardComplexIso (d.symm ≪≫ c.symm ≪≫ e)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))
  exact ⟨(F.mapDerivedCategorySingleFunctor 0).app M ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app (F.obj M) ≪≫ e'⟩

/-- Closed direct image preserves cokernels, hence finite colimits. -/
private theorem closedDirectImageColimits {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    Limits.PreservesFiniteColimits
      (RingedSpace.moduleDirectImage i.toLRSHom.toShHom) := by
  let F := RingedSpace.moduleDirectImage i.toLRSHom.toShHom
  have {A B : SheafOfModules.{u} (moduleRings Z.toRingedSpace)} (f : A ⟶ B) :
      Limits.PreservesColimit (Limits.parallelPair f 0) F := by
    exact Scheme.Modules.closedImmersion_pushforward_preservesCokernel i f
  exact Functor.preservesFiniteColimits_of_preservesCokernels F

/-- A perfect single pushforward of O_Z gives a perfect standard Ri_* of the unit
(Stacks, Tags 05RU, 08CM and 0A9U). -/
theorem perfectImmersion_standardPerfection
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hperfect : Y.IsPerfect
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))) :
    @Scheme.IsPerfect Y (HasDerivedCategory.standard _)
      (fun _ ↦ HasDerivedCategory.standard _)
      ((@schemeDerivedDirectImage Z Y (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) i).obj
        (𝟙_ (@schemeDerivedCategory Z (HasDerivedCategory.standard _)))) := by
  have h := standardSinglePerfect Y _ hperfect
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let F := RingedSpace.moduleDirectImage i.toLRSHom.toShHom
  let : Limits.PreservesFiniteColimits F := closedDirectImageColimits i
  let : Limits.PreservesFiniteLimits F := by
    dsimp [F, RingedSpace.moduleDirectImage]
    infer_instance
  let eunit : 𝟙_ (schemeDerivedCategory Z) ≅
      (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit Z.ringCatSheaf) :=
    (DerivedCategory.quotientCompQhIso _).app _
  let e := (schemeDerivedDirectImage i).mapIso eunit ≪≫
    F.singleFunctorCompRightDerivedFunctorIso.app (SheafOfModules.unit Z.ringCatSheaf)
  intro x
  obtain ⟨U, hx, K, hK, ⟨c⟩⟩ := h x
  refine ⟨U, hx, K, hK, ?_⟩
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))
  exact ⟨(SheafOfModules.overFunctor.{u}
    (moduleRings Y.toRingedSpace) U).mapDerivedCategory.mapIso e ≪≫ c⟩

end AlgebraicGeometry
