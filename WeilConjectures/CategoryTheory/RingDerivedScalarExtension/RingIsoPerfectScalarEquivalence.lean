/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingDerivedScalarExtension.RingDerivedScalarExtension
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Perfect scalar transport along a ring isomorphism
Source: HRS Proposition 4.3(3); Stacks Project Tag 06Y6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe r wA wB
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingDerivedScalarExtension

private theorem perfect_of_iso {R : Type r} [CommRing R]
    [HasDerivedCategory.{wA} (ModuleCat.{r} R)]
    {K L : DerivedCategory (ModuleCat.{r} R)}
    (h : DerivedCategory.IsPerfectRingComplex K) (e : K ≅ L) :
    DerivedCategory.IsPerfectRingComplex L := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨i⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ i⟩⟩

private theorem perfect_restrict (A B : CommRingCat.{r}) (e : A ≃+* B)
    [HasDerivedCategory.{wA} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{r} B)]
    (K : DerivedCategory (ModuleCat.{r} B)) (hK : DerivedCategory.IsPerfectRingComplex K) :
    DerivedCategory.IsPerfectRingComplex
      ((ModuleCat.restrictScalars.{r} e.toRingHom).mapDerivedCategory.obj K) := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨i⟩⟩ := hK
  let F := ModuleCat.restrictScalars.{r} e.toRingHom
  let P' := (F.mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨P', a, b, ?_, ?_, ?_,
    ⟨F.mapDerivedCategory.mapIso i ≪≫ F.mapDerivedCategoryFactors.app P⟩⟩
  · exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff P F a).mpr ha
  · exact (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff P F b).mpr hb
  · intro n
    let M := P.X n
    let N := F.obj M
    let : RingHomInvPair e.symm.toRingHom e.toRingHom :=
      ⟨by ext x; simp, by ext x; simp⟩
    let : RingHomInvPair e.toRingHom e.symm.toRingHom :=
      ⟨by ext x; simp, by ext x; simp⟩
    let se : LinearEquiv e.symm.toRingHom (σ' := e.toRingHom) M N :=
      { Equiv.refl _ with
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          change r • x = e (e.symm r) • x
          rw [e.apply_symm_apply] }
    have := (hP n).1
    have := (hP n).2
    exact ⟨Module.Projective.of_equiv se,
      Module.Finite.of_surjective se.toLinearMap se.surjective⟩

end CategoryTheory.RingDerivedScalarExtension
