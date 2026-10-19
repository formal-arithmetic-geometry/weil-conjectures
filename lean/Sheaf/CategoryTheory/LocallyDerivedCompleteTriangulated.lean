/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction

/-!
# Triangulated closure of locally derived complete objects

Source: Stacks Tags 0999 and 08JC; Bhatt--Scholze, Definition 6.5.1.
(blueprint: lem-sfb-local-completeness-triangulated).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace CategoryTheory


/-- Local derived completeness is invariant under isomorphisms and defines a full
triangulated subcategory, without finiteness assumptions on the ideal or site.
Source: Stacks Tags 0999 and 08JC; Bhatt--Scholze, following Definition 6.5.1.
(blueprint: lem-sfb-local-completeness-triangulated).

Proof: For every slice and ideal section, compose slice restriction with internal
Hom from its localization. Both functors are exact and commute with shifts. Their
zero kernels contain zero, are invariant under isomorphisms and shifts, and are
closed under extensions by the distinguished-triangle zero criterion. Intersect
these kernels over all the tested sections. -/
theorem locallyDerivedRingedIdealComplete_triangulated
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsLocallyDerivedRingedIdealComplete O I ι) ∧
      ObjectProperty.IsTriangulated (IsLocallyDerivedRingedIdealComplete O I ι) := by
  let P : ObjectProperty (ringedSiteDerived O) := IsLocallyDerivedRingedIdealComplete O I ι
  have hi : P.IsClosedUnderIsomorphisms := ⟨by
    intro E E' e h U f hf
    exact (h U f hf).of_iso
      ((derivedInternalHom (J.over U) (O.over U)).mapIso
        ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e))).symm⟩
  have := hi
  have (U : C) : (ringedDerivedRestriction O U).Additive := by
    dsimp only [ringedDerivedRestriction]
    infer_instance
  let (U : C) : (ringedDerivedRestriction O U).CommShift ℤ := by
    dsimp only [ringedDerivedRestriction]
    infer_instance
  have (U : C) : (ringedDerivedRestriction O U).IsTriangulated := by
    dsimp only [ringedDerivedRestriction]
    infer_instance
  have hz : P 0 := by
    intro U f hf
    let L := (DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))
    obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (O.over U)).1 L
    let := s
    have := hs
    exact ((Functor.curry.obj (derivedInternalHom (J.over U) (O.over U))).obj
      (op L)).map_isZero ((ringedDerivedRestriction O U).map_isZero (isZero_zero _))
  have hshift (E : ringedSiteDerived O) (n : ℤ) (h : P E) : P (E⟦n⟧) := by
    intro U f hf
    let L := (DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))
    let H := (Functor.curry.obj (derivedInternalHom (J.over U) (O.over U))).obj (op L)
    obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (O.over U)).1 L
    let := s
    have := hs
    let R := ringedDerivedRestriction O U
    exact ((shiftFunctor _ n).map_isZero (h U f hf)).of_iso
      (H.mapIso ((R.commShiftIso n).app E) ≪≫ (H.commShiftIso n).app (R.obj E))
  have hext (T : Triangle (ringedSiteDerived O)) (hT : T ∈ distTriang _)
      (h₁ : P T.obj₁) (h₃ : P T.obj₃) : P T.obj₂ := by
    intro U f hf
    let L := (DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))
    let H := (Functor.curry.obj (derivedInternalHom (J.over U) (O.over U))).obj (op L)
    obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (O.over U)).1 L
    let := s
    have := hs
    let R := ringedDerivedRestriction O U
    exact Triangle.isZero₂_of_isZero₁₃ ((R ⋙ H).mapTriangle.obj T)
      ((R ⋙ H).map_distinguished T hT) (h₁ U f hf) (h₃ U f hf)
  have : P.ContainsZero := ⟨0, isZero_zero _, hz⟩
  have : P.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨fun E h ↦ hshift E n h⟩⟩
  exact ⟨hi, { toIsTriangulatedClosed₂ := .mk' hext }⟩

end CategoryTheory
