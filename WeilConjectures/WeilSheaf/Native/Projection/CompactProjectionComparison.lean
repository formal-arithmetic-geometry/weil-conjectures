/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.BoundedOpenProjectionSquare
public import WeilConjectures.WeilSheaf.Native.Projection.BoundedProperProjectionSquare
public import WeilConjectures.WeilSheaf.Native.Projection.MateAdjunctionChoice
public import WeilConjectures.WeilSheaf.Native.Projection.TwoSquareComposite
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionPastingMonoidal

/-! # The normalized compact-support projection and forget comparisons -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance] Compactification.over

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

local notation "c" => nativeProjectionCompactification k₀ f
local notation "cb" => geometricFiberHomCompactification (k₀ := k₀) f
local notation "fb" => geometricFiberHom (k₀ := k₀) f
local notation "Λ" => Profinite.padicAlgClRingObj l

local instance : QuasiCompact (c).i := (c).quasiCompact_openImmersion inferInstance

/-- The pullback compositor on bounded Weil complexes. -/
def projectionBoundedPullComp : upperStar (c).g ⋙ upperStar (c).i ≅ upperStar (k₀ := k₀) (l := l) f :=
  ((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (objectProperty k₀ l Y).ι (nativeProjectionPullComp k₀ l f))

/-- The geometric pullback compositor through the chosen Weil compactification. -/
def projectionGeometricPullComp :
    CondensedRing.boundedConstructibleUpperStar Λ l (cb).overG ⋙
        CondensedRing.boundedConstructibleUpperStar Λ l (cb).overI ≅
      CondensedRing.boundedConstructibleUpperStar Λ l fb :=
  ((boundedConstructible _).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (boundedConstructible _).ι
      (CondensedRing.leftDerivedUpperStarOverCompactificationIso Λ cb).symm)

/-- The geometric pullback compositor has the canonical ambient component. -/
lemma projectionGeometricPullComp_hom_app
    (N : BoundedConstructible (condensedRingObj Λ
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :
    (ObjectProperty.ι _).map
      ((projectionGeometricPullComp k₀ l f).hom.app N) =
      (CondensedRing.leftDerivedUpperStarOverCompactificationIso Λ cb).inv.app N.obj := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Forget comparison for the compactification induced from the Weil category. -/
def projectionCompactificationForgetIso :
    derivedLowerShriek k₀ l f ⋙ compactProjectionForget k₀ l Y ≅
      compactProjectionForget k₀ l X ⋙
        CondensedRing.boundedConstructibleLowerShriekOfCompactification l cb := by
  let e₁ := Functor.isoWhiskerLeft (extensionByZero (c).i)
    (projectionProperForgetIso k₀ l (c).g)
  let G' := CondensedRing.boundedConstructibleLowerStar l (cb).overG
  let e₂ := Functor.isoWhiskerRight (projectionOpenForgetIso k₀ l (c).i)
    G'
  let e := e₁ ≪≫ e₂
  exact e

/-- The inverse compactification comparison is the stacked square, including its final identity. -/
lemma projectionCompactificationForgetIso_inv_app_id (M : WeilComplex k₀ l X) :
    (projectionCompactificationForgetIso k₀ l f).inv.app M =
      (CondensedRing.boundedConstructibleLowerStar l (cb).overG).map
        ((projectionOpenForgetIso k₀ l (c).i).inv.app M) ≫
      (projectionProperForgetIso k₀ l (c).g).inv.app ((extensionByZero (c).i).obj M) ≫
      (compactProjectionForget k₀ l Y).map (𝟙 ((derivedLowerShriek k₀ l f).obj M)) := by
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback comparison obtained by pasting the open and proper comparisons. -/
def projectionCompactPullForgetIso :
    upperStar f ⋙ compactProjectionForget k₀ l X ≅
      compactProjectionForget k₀ l Y ⋙ CondensedRing.boundedConstructibleUpperStar Λ l fb := by
  let e₁ := Functor.isoWhiskerRight (projectionBoundedPullComp k₀ l f).symm
    (compactProjectionForget k₀ l X)
  let e₂ := Functor.isoWhiskerLeft (upperStar (c).g)
    (compactProjectionForgetUpperStarIso k₀ l (c).i)
  let P' := CondensedRing.boundedConstructibleUpperStar Λ l (cb).overI
  let e₃ := Functor.isoWhiskerRight (compactProjectionForgetUpperStarIso k₀ l (c).g)
    P'
  let e₄ := Functor.isoWhiskerLeft (compactProjectionForget k₀ l Y)
    (projectionGeometricPullComp k₀ l f)
  let e := e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄
  exact e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The compact projection isomorphism, with both factors canonically normalized. -/
def projectionCompactIso : nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f := by
  let e := projectionCompositeIso
    (I := extensionByZero (k₀ := k₀) (l := l) (c).i)
    (G := derivedLowerStar (k₀ := k₀) (l := l) (c).g)
    (P := upperStar (k₀ := k₀) (l := l) (c).i)
    (Q := upperStar (k₀ := k₀) (l := l) (c).g)
    (TC := nativeConstructibleTensor k₀ l X)
    (TD := nativeConstructibleTensor k₀ l (c).Z)
    (TE := nativeConstructibleTensor k₀ l Y)
    (nativeBoundedOpenProjectionIso (c).i) (nativeBoundedProperProjectionIso (c).g)
    (projectionBoundedPullComp k₀ l f)
  exact e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The compact projection isomorphism lies over the geometric projection map for the
base-changed compactification. -/
theorem projectionCompactification_forget_square (M : WeilComplex k₀ l X)
    (N : WeilComplex k₀ l Y) :
    (compactProjectionForget k₀ l Y).map ((projectionCompactIso k₀ l f).hom.app (M, N)) ≫
        (projectionCompactificationForgetIso k₀ l f).hom.app _ ≫
        (CondensedRing.boundedConstructibleLowerShriekOfCompactification l cb).map
          ((compactProjectionForgetTensorIso k₀ l X).hom.app (M, (upperStar f).obj N) ≫
            (compactProjectionForget k₀ l X).obj M ◁
              (projectionCompactPullForgetIso k₀ l f).hom.app N) =
      (compactProjectionForgetTensorIso k₀ l Y).hom.app ((derivedLowerShriek k₀ l f).obj M, N) ≫
        (projectionCompactificationForgetIso k₀ l f).hom.app M ▷
          (compactProjectionForget k₀ l Y).obj N ≫
        ObjectProperty.homMk
          (X := (CondensedRing.boundedConstructibleLowerShriekOfCompactification l cb).obj
            ((compactProjectionForget k₀ l X).obj M) ⊗ (compactProjectionForget k₀ l Y).obj N)
          (Y := (CondensedRing.boundedConstructibleLowerShriekOfCompactification l cb).obj
            ((compactProjectionForget k₀ l X).obj M ⊗
              (CondensedRing.boundedConstructibleUpperStar Λ l fb).obj
                ((compactProjectionForget k₀ l Y).obj N)))
          (CondensedRing.exceptionalProjectionMorphismOfCompactification Λ cb
            ((compactProjectionForget k₀ l X).obj M).obj
            ((compactProjectionForget k₀ l Y).obj N).obj) := by
  have hε := projectionGeometricPullComp_hom_app k₀ l f
    ((compactProjectionForget k₀ l Y).obj N)
  have hp := CondensedRing.homMk_exceptionalProjectionMorphismOfCompactification_eq (f := fb) l cb
    ((compactProjectionForget k₀ l X).obj M) ((compactProjectionForget k₀ l Y).obj N)
    ((projectionGeometricPullComp k₀ l f).hom.app ((compactProjectionForget k₀ l Y).obj N)) hε
  rw [hp]
  -- the pasted square, with all spelling conversions done on abstract functors
  have hpaste := projectionForgetSquare_paste_monoidal
    (projectionOpenForgetIso k₀ l (c).i) (projectionProperForgetIso k₀ l (c).g)
    (compactProjectionForgetUpperStarIso k₀ l (c).i)
    (compactProjectionForgetUpperStarIso k₀ l (c).g)
    (compactProjectionForgetTensorIso k₀ l X) (compactProjectionForgetTensorIso k₀ l (c).Z)
    (compactProjectionForgetTensorIso k₀ l Y)
    (projectionBoundedPullComp k₀ l f) (projectionGeometricPullComp k₀ l f)
    _ _ _ _ (projectionForgetSquare_open k₀ l (c).i) (projectionForgetSquare_proper k₀ l (c).g)
    (projectionCompactIso k₀ l f).hom (projectionCompactificationForgetIso k₀ l f)
    (projectionCompactPullForgetIso k₀ l f) M N
    (projectionCompositeIso_hom_app (nativeBoundedOpenProjectionIso (c).i)
      (nativeBoundedProperProjectionIso (c).g) (projectionBoundedPullComp k₀ l f) M N)
    (fun _ ↦ rfl) rfl
  exact hpaste

/-- The exceptional mate of the normalized compactification comparison is invertible. -/
theorem isIso_mateEquiv_projectionCompactificationForgetIso
    {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l f ⊣ R) :
    IsIso (mateEquiv adj
      (CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction l cb)
      (projectionCompactificationForgetIso k₀ l f).inv).natTrans := by
  have : (derivedLowerStar (k₀ := k₀) (l := l) (c).g).IsLeftAdjoint :=
    isLeftAdjoint_derivedLowerStar_of_isProper (c).g
  let ai := extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) (c).i
  let bi := CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l (cb).overI
  let ag := Adjunction.ofIsLeftAdjoint (derivedLowerStar (k₀ := k₀) (l := l) (c).g)
  let bg := Adjunction.ofIsLeftAdjoint (CondensedRing.boundedConstructibleLowerStar l (cb).overG)
  have : IsIso (mateEquiv ai bi (projectionOpenForgetIso k₀ l (c).i).inv).natTrans :=
    isIso_mateEquiv_projectionOpenForgetIso k₀ l (c).i
  have : IsIso (mateEquiv ag bg (projectionProperForgetIso k₀ l (c).g).inv).natTrans :=
    isIso_mateEquiv_projectionProperForgetIso k₀ l (c).g ag bg
  let e : derivedLowerShriek k₀ l f ≅ extensionByZero (c).i ⋙ derivedLowerStar (c).g :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) (fun φ ↦ by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl)
  let e' := Iso.refl (CondensedRing.boundedConstructibleLowerShriekOfCompactification l cb)
  have h := isIso_mateEquiv_vComp_whiskerLeft_whiskerRight ai bi ag bg adj
    (CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction l cb)
    e e' (projectionOpenForgetIso k₀ l (c).i).inv (projectionProperForgetIso k₀ l (c).g).inv
  -- identify the stacked square with the compactification comparison, by components
  rw [TwoSquare.vComp_whiskerLeft_whiskerRight_eq e e'
    (TwoSquare.mk _ _ _ _ (projectionOpenForgetIso k₀ l (c).i).inv)
    (TwoSquare.mk _ _ _ _ (projectionProperForgetIso k₀ l (c).g).inv)
    (TwoSquare.mk _ _ _ _ (projectionCompactificationForgetIso k₀ l f).inv) (fun M ↦ by
      simp only [e, e', NatIso.ofComponents_inv_app, Iso.refl_inv, Iso.refl_hom,
        NatTrans.id_app, Category.id_comp]
      exact projectionCompactificationForgetIso_inv_app_id k₀ l f M)] at h
  exact h

end AlgebraicGeometry.WeilComplex
