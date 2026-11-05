/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyProduct

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem fan_projection_isIso
    {A : Type*} [Category A] [HasZeroMorphisms A]
    {I : Type*} {F : I → A} {H : A}
    (g : ∀ i, H ⟶ F i) (hg : IsLimit (Fan.mk H g))
    (j : I) (hz : ∀ i, i ≠ j → IsZero (F i)) : IsIso (g j) := by
  classical
  let v : F j ⟶ H := Fan.IsLimit.lift hg
    (fun i ↦ if h : j = i then eqToHom (congrArg F h) else 0)
  have hv : ∀ i, v ≫ g i = if h : j = i then eqToHom (congrArg F h) else 0 :=
    fun i ↦ Fan.IsLimit.fac hg _ i
  refine ⟨⟨v, ?_, ?_⟩⟩
  · apply Fan.IsLimit.hom_ext hg
    intro i
    by_cases hi : i = j
    · subst i
      simp [Category.assoc, hv]
    · exact (hz i hi).eq_of_tgt _ _
  · simpa using hv j

private theorem homObj_isZero_right
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (A B : SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hB : IsZero B) : IsZero (SheafOfModules.homObj (R := R) A B) := by
  apply (IsZero.iff_id_eq_zero _).2
  rw [← SheafOfModules.homObjMap_id (R := R)]
  rw [hB.eq_of_src (𝟙 B) 0]
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 A.val) ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map 0 = 0
  ext W x
  rfl

end CategoryTheory
