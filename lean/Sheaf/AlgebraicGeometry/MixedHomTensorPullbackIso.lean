/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
import all Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatTensorProduct
import Sheaf.Algebra.Homology.KFlatPullback

/-! # Normalized pullback tensor isomorphism
Source: Stacks Project, Tags 079U and 0B6I.
(blueprint: lem-sc-mixed-hom-tensor-pullback-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The canonical pullback tensor comparison with independent localization universes.
Proof: take the canonical comparison normalized to SingleComplexBaseChange.counit.
On K-flat representatives, tensor, pullback, localization tensor maps and the shared
left-derived counits are invertible. The canonical coordinate equation thus makes
its components invertible. K-flat resolutions and naturality transport invertibility
to arbitrary objects. Package these components as a natural isomorphism.
Source: Stacks Tags 079U and 0B6I
(blueprint: lem-sc-mixed-hom-tensor-pullback-iso). -/
theorem exists_mixedHomTensorPullbackIso {T S : Scheme.{u}} (h : T ⟶ S) :
    ∃ t : tensor (schemeDerivedCategory S) ⋙ derivedPullback h ≅
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T),
      IsCanonicalPullbackTensorComparison h (fun K L ↦ t.hom.app (K, L)) := by
  obtain ⟨τ, hτ⟩ := exists_canonicalPullbackTensorComparison h
  let c : tensor (schemeDerivedCategory S) ⋙ derivedPullback h ⟶
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T) :=
    { app := fun Z ↦ τ Z.1 Z.2
      naturality := fun Z Z' a ↦ hτ.2 Z.1 Z'.1 Z.2 Z'.2 a.1 a.2 }
  have hflat (P N : CochainComplex
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (hP : P.IsKFlat) (hN : N.IsKFlat) :
      IsIso (c.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) := by
    let : MonoidalCategory (SheafOfModules.{u} (moduleRings S.toRingedSpace)) :=
      SheafOfModules.monoidalCategory S.sheaf
    let : MonoidalCategory (SheafOfModules.{u} (moduleRings T.toRingedSpace)) :=
      SheafOfModules.monoidalCategory T.sheaf
    obtain ⟨φ, _, hφ⟩ := hτ.1 P N hP hN
    have htot := CochainComplex.IsKFlat.mapBifunctor
      (X := S.toRingedSpace) P N hP hN
    have hpull : CochainComplex.IsKFlat (R := T.sheaf)
        (((Scheme.Modules.tensorPullback h).mapHomologicalComplex (.up ℤ)).obj P) := by
      convert CochainComplex.isKFlat_pullback h.base T.sheaf S.sheaf ⟨h.c⟩ P hP using 1
      rfl
    have := pullbackTensorModelMap_isIso S P N hP
    have := pullbackTensorModelMap_isIso T
      (((Scheme.Modules.tensorPullback h).mapHomologicalComplex (.up ℤ)).obj P)
      (((Scheme.Modules.tensorPullback h).mapHomologicalComplex (.up ℤ)).obj N) hpull
    have := pullbackCounit_isIso h P hP
    have := pullbackCounit_isIso h N hN
    have := pullbackCounit_isIso h (pullbackTensorTotal S P N) htot
    have hi : IsIso (τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) ≫
        ((SingleComplexBaseChange.counit h).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
        (SingleComplexBaseChange.counit h).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
        pullbackTensorModelMap T
          (((Scheme.Modules.tensorPullback h).mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback h).mapHomologicalComplex (.up ℤ)).obj N)) := by
      rw [← hφ]
      infer_instance
    change IsIso (τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N))
    exact IsIso.of_isIso_comp_right _
      (((SingleComplexBaseChange.counit h).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
        (SingleComplexBaseChange.counit h).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
        pullbackTensorModelMap T
          (((Scheme.Modules.tensorPullback h).mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback h).mapHomologicalComplex (.up ℤ)).obj N))
  have hc (Z : schemeDerivedCategory S × schemeDerivedCategory S) : IsIso (c.app Z) := by
    let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolution (R := S.sheaf) (Q.objPreimage Z.1)
    obtain ⟨N, t, hN, _, ht, _⟩ :=
      CochainComplex.exists_isKFlatResolution (R := S.sheaf) (Q.objPreimage Z.2)
    have := hs
    have := ht
    let eP : Q.obj P ≅ Z.1 := asIso (Q.map s) ≪≫ Q.objObjPreimageIso Z.1
    let eN : Q.obj N ≅ Z.2 := asIso (Q.map t) ≪≫ Q.objObjPreimageIso Z.2
    let e : (Q.obj P, Q.obj N) ≅ Z :=
      { hom := (eP.hom, eN.hom)
        inv := (eP.inv, eN.inv)
        hom_inv_id := by ext <;> simp
        inv_hom_id := by ext <;> simp }
    exact (NatTrans.isIso_app_iff_of_iso c e).mp (hflat P N hP hN)
  have (Z : schemeDerivedCategory S × schemeDerivedCategory S) := hc Z
  exact ⟨NatIso.ofComponents (fun Z ↦ asIso (c.app Z))
    (fun a ↦ c.naturality a), hτ⟩

/-- The pullback tensorator normalized to the shared derived counit.
Source: Stacks Tag 079U. -/
def mixedHomTensorPullbackIso {T S : Scheme.{u}} (h : T ⟶ S) :
    tensor (schemeDerivedCategory S) ⋙ derivedPullback h ≅
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T) :=
  Classical.choose (exists_mixedHomTensorPullbackIso h)

end AlgebraicGeometry
