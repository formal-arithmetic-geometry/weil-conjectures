/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Exact computation of pullback along scheme isomorphisms

## References

* Stacks Project, Tags 0D5S and 0098.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- The pinned derived tensor-pullback counit is invertible on K-flat complexes. -/
theorem counit_isIso_kFlat
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Z.sheaf) P) :
    IsIso ((counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      (derivedPullback_spec j)
  have h : E = Scheme.Modules.tensorPullback j :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)
  have : (derivedPullback j).IsLeftDerivedFunctor ε W := hL
  have hc : (derivedPullback j).IsLeftDerivedFunctor (counit j) W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) j
  have : IsIso ((derivedPullback j).leftDerivedLift ε W
      (derivedPullback j) (counit j)) :=
    ((derivedPullback j).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      ε W (derivedPullback j) (counit j)).mp hc
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hK P hP
  rw [← Functor.leftDerived_fac_app (derivedPullback j) ε W
    (derivedPullback j) (counit j)]
  infer_instance

/-- The pinned derived tensor-pullback counit is invertible on every complex
when the scheme morphism is invertible. -/
theorem isIso_counit_of_isIso
    [d : ∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (M : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
    IsIso ((counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj M))  := by
  classical
  let : HasDerivedCategory.{w} Y.Modules := d Y
  let : HasDerivedCategory.{w} Z.Modules := d Z
  let T := Scheme.Modules.tensorPullback j
  let R := Scheme.Modules.restrictFunctor j
  let e : T ≅ R :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
      (Scheme.Modules.restrictAdjunction j)
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso e.symm
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := Z.sheaf) M
  have : QuasiIso s := hs
  have hsT : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map s) := inferInstance
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)
  have hq : IsIso (DerivedCategory.Qh.map (q.map s)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mpr hs
  have ht : IsIso (DerivedCategory.Qh.map
      ((T.mapHomotopyCategory (.up ℤ)).map (q.map s))) := by
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((T.mapHomologicalComplex (.up ℤ)).map s)))
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hsT
  have hp := counit_isIso_kFlat j P hP
  have hn := (counit j).naturality (q.map s)
  dsimp only [Functor.comp_map] at hn
  have hcomp : IsIso ((derivedPullback j).map (DerivedCategory.Qh.map (q.map s)) ≫
      (counit j).app (q.obj M)) := by
    rw [hn]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hcomp

end AlgebraicGeometry.SingleComplexBaseChange
