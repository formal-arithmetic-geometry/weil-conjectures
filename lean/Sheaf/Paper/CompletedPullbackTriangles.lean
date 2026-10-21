/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.PbcActualStrictPullback

/-! # Completed pullback preserves shifts and distinguished triangles
Source: literature/stacks-project/proetale.tex, Tag 099N (2),(5), with
`derived.tex`, Tag 05SE, and `sites-cohomology.tex`, Tag 0941
(blueprint: lem-cbc-completed-pullback-triangles).

The specified strict-tower completed pullback has coherent shift comparisons,
and it carries distinguished triangles whose vertices are intrinsically derived
complete to distinguished image triangles.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
variable (d : AdicCoefficientDatum A)

private theorem reflective_triangulated {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : ObjectProperty C) (F : C ⥤ C) (η : 𝟭 C ⟶ F)
    [F.CommShift ℤ] [NatTrans.CommShift η ℤ]
    (hout : ∀ X, P (F.obj X))
    (hfix : ∀ X, P X ↔ IsIso (η.app X))
    (href : ∀ X L, P L → Function.Bijective (fun f : F.obj X ⟶ L ↦ η.app X ≫ f)) :
    P.IsTriangulated := by
  have hshift (X : C) (n : ℤ) :
      (η.app X)⟦n⟧' = η.app (X⟦n⟧) ≫ (F.commShiftIso n).hom.app X := by
    simpa using NatTrans.shift_app_comm η n X
  have : P.IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro X hX
    apply (hfix _).mpr
    have := (hfix X).mp hX
    rw [NatTrans.app_shift η n X]
    infer_instance
  have hle : P ≤ P.leftOrthogonal.rightOrthogonal := fun _ hX _ f hL ↦ hL f hX
  have heq : P = P.leftOrthogonal.rightOrthogonal := by
    apply le_antisymm hle
    intro X hX
    obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle (η.app X)
    let T := Triangle.mk (η.app X) g δ
    have hZ : P.leftOrthogonal Z := by
      intro L f hL
      have hgf : g ≫ f = 0 := by
        apply (href X L hL).1
        change η.app X ≫ (g ≫ f) = η.app X ≫ 0
        rw [← Category.assoc]
        have hzero : η.app X ≫ g = 0 := comp_distTriang_mor_zero₁₂ T hT
        simp only [hzero, zero_comp, comp_zero]
      obtain ⟨a, ha⟩ := Triangle.yoneda_exact₃ T hT f hgf
      obtain ⟨b, hb⟩ := (href (X⟦(1 : ℤ)⟧) L hL).2 a
      have hab : a = (η.app X)⟦(1 : ℤ)⟧' ≫
          ((F.commShiftIso (1 : ℤ)).inv.app X ≫ b) := by
        rw [hshift]
        simpa [Category.assoc] using hb.symm
      rw [ha, hab, ← Category.assoc]
      have hzero : δ ≫ (η.app X)⟦(1 : ℤ)⟧' = 0 :=
        comp_distTriang_mor_zero₃₁ T hT
      simpa [T] using congrArg (fun z ↦ z ≫
        ((F.commShiftIso (1 : ℤ)).inv.app X ≫ b)) hzero
    have hR := hle _ (hout X)
    have hZ' : P.leftOrthogonal.rightOrthogonal Z :=
      P.leftOrthogonal.rightOrthogonal.ext_of_isTriangulatedClosed₃ T hT hX hR
    have hz : IsZero Z := (IsZero.iff_id_eq_zero Z).mpr (hZ' (𝟙 Z) hZ)
    apply (hfix X).mpr
    exact (Triangle.isZero₃_iff_isIso₁ T hT).mp hz
  rw [heq]
  infer_instance

private theorem complete_iso (Y : AlgebraicGeometry.Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ObjectProperty.IsClosedUnderIsomorphisms (PbcIsIntrinsicallyComplete Y d) := by
  constructor
  intro K L e hK
  obtain ⟨r, f, hf, C, eC, hC⟩ := hK
  refine ⟨r, f, hf, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison Y d).inv).mapIso e, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

private theorem complete_tri (Y : AlgebraicGeometry.Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ObjectProperty.IsTriangulated (PbcIsIntrinsicallyComplete Y d) := by
  let P : ObjectProperty (PbcCompletedDerived Y d) := PbcIsIntrinsicallyComplete Y d
  let F := pbcActualCompletion d Y
  let η := pbcActualCompletionUnit d Y
  let adj := Adjunction.ofIsRightAdjoint P.ι
  have := complete_iso Y d
  have : NatTrans.CommShift η ℤ :=
    (pbcActualCompletionShift_exists d Y).exists.choose_spec
  apply reflective_triangulated P F η
  · intro X
    exact (P.ι.leftAdjoint.obj X).property
  · intro X
    rw [show IsIso (η.app X) ↔ P.ι.essImage X from
      adj.isIso_unit_app_iff_mem_essImage]
    constructor
    · intro h
      exact ⟨⟨X, h⟩, ⟨Iso.refl _⟩⟩
    · rintro ⟨L, ⟨e⟩⟩
      exact P.prop_of_iso e L.property
  · intro X L hL
    have hb := (ObjectProperty.isLocal_adj_unit_app adj X) L ⟨⟨L, hL⟩, rfl⟩
    exact hb


set_option linter.unusedVariables false in
/-- The strict-tower completed pullback has coherent shifts and preserves
ambient distinguished triangles on intrinsically derived-complete vertices.
Source: literature/stacks-project/proetale.tex, Tag 099N (2),(5), with
`derived.tex`, Tag 05SE, and `sites-cohomology.tex`, Tag 0941
(blueprint: lem-cbc-completed-pullback-triangles).

Proof:
1. The additive reduction-tower construction preserves shifts and mapping cones.
K-flat resolutions and invariance on resolving quasi-isomorphisms are supplied
by `def-weil-pbc-adic-coefficient-datum`. Apply
`lem-pur-left-derived-from-kflat-class` to obtain the exact reduction functor R.
2. Levelwise module pullback along the specified completed coefficient map is
additive, so preserves the shift signs and cone differential matrix.
`lem-weil-pbc-diagram-kflat-replacements` gives strict objectwise K-flat
flat-term replacements and quasi-isomorphism invariance. The same resolving-class
theorem makes its total derived functor V exact; no underived flatness is assumed.
3. By `prop-weil-pbc-rlim-functoriality`, strict-tower derived inverse limit L
is exact. Thus LVR sends the ambient distinguished triangle to a distinguished
triangle. `pbcActualCompletedPullback_tower` in the recorded completed-pullback
dependency identifies its restriction to complete inputs, naturally and with
its quotient augmentation, with the completion-reflector presentation
`pbcActualCompletedPull` used here. Transport the triangle along that comparison.
4. The tensor, product and mapping-fiber formulas defining intrinsic completion
commute with shifts, including its unit, so the complete-object domain is stable
under shifts. Iterate the three exact-functor comparisons for positive integers,
use inverse comparisons for negative integers and the identity for zero.
Compose them as LV(sigma_R), L(sigma_V), sigma_L. Naturality and the zero and
addition identities follow from those of the factors; in mixed signs inverse
factors cancel. The last arrow is the image of the original last arrow followed
by this comparison at 1, exactly as in mapTriangle. The completion-reflector
presentation has the corresponding unit-normalized ordinary-pullback/completion
shift structure on the ambient category; on complete inputs the natural
unit-compatible comparison identifies it with this tower construction.
No constructibility or Noetherian hypothesis on the schemes is used.
-/
theorem completedPullback_preserves_shifts_distinguished
    (g : X ⟶ Y) (d : AdicCoefficientDatum A) :
    ∃ h : (pbcActualCompletedPull g d).CommShift ℤ,
      (fun [shift : (pbcActualCompletedPull g d).CommShift ℤ] ↦
        ∀ (T : Triangle (PbcCompletedDerived Y d)),
          T ∈ distTriang _ →
          PbcIsIntrinsicallyComplete Y d T.obj₁ →
          PbcIsIntrinsicallyComplete Y d T.obj₂ →
          PbcIsIntrinsicallyComplete Y d T.obj₃ →
          (pbcActualCompletedPull g d).mapTriangle.obj T ∈ distTriang _)
        (shift := h) := by
  let P : ObjectProperty (PbcCompletedDerived X d) := PbcIsIntrinsicallyComplete X d
  have : P.IsTriangulated := complete_tri X d
  let adj := Adjunction.ofIsRightAdjoint P.ι
  let : P.ι.leftAdjoint.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : P.ι.leftAdjoint.IsTriangulated := adj.isTriangulated_leftAdjoint
  let : (pbcActualCompletion d X).CommShift ℤ :=
    inferInstanceAs ((P.ι.leftAdjoint ⋙ P.ι).CommShift ℤ)
  have : (pbcActualCompletion d X).IsTriangulated :=
    inferInstanceAs ((P.ι.leftAdjoint ⋙ P.ι).IsTriangulated)
  let : (pbcActualDerivedPush g d).CommShift ℤ :=
    Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt (pbcActualModulePush g d)
  have : (pbcActualDerivedPush g d).IsTriangulated :=
    Functor.instIsTriangulatedDerivedCategoryRightDerivedFunctor (pbcActualModulePush g d)
  let pullAdj := pbcActualDerivedAdjunction g d
  let : (pbcActualDerivedPull g d).CommShift ℤ := pullAdj.leftAdjointCommShift ℤ
  have : pullAdj.CommShift ℤ := pullAdj.commShift_of_rightAdjoint ℤ
  have : (pbcActualDerivedPull g d).IsTriangulated := pullAdj.isTriangulated_leftAdjoint
  let : (pbcActualCompletedPull g d).CommShift ℤ :=
    inferInstanceAs ((pbcActualDerivedPull g d ⋙ pbcActualCompletion d X).CommShift ℤ)
  have : (pbcActualCompletedPull g d).IsTriangulated :=
    inferInstanceAs ((pbcActualDerivedPull g d ⋙ pbcActualCompletion d X).IsTriangulated)
  refine ⟨inferInstance, ?_⟩
  intro T hT _ _ _
  exact (pbcActualCompletedPull g d).map_distinguished T hT

end AlgebraicGeometry.Scheme
