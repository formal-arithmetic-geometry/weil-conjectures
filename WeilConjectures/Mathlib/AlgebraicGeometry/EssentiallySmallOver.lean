/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Schemes affine and of finite type over a base form an essentially small category

Let `Y` be a scheme. A `Y`-scheme `X ⟶ Y` is the colimit of its restrictions `X ×_Y U` to the
affine opens `U` of `Y` (`AlgebraicGeometry.Scheme.Over.nonempty_iso_of_restrictAffineOpens_iso`).
If `X ⟶ Y` is affine and locally of finite type, these restrictions are affine schemes locally of
finite type over `Y`, which form an essentially small category
(`AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec`). Hence the `Y`-schemes affine and
locally of finite type over `Y` form an essentially small family
(`AlgebraicGeometry.Scheme.Over.small_skeleton_isAffineHomLocallyOfFiniteType`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Over

variable {Y : Scheme.{u}}

/-- The restrictions `X ×_Y U ⟶ Y` of a `Y`-scheme `X` to the affine opens `U` of `Y`, as a
diagram of `Y`-schemes indexed by the affine opens. -/
noncomputable def restrictAffineOpens (X : Over Y) : Y.affineOpens ⥤ Over Y :=
  (Cover.functorOfLocallyDirected (Y.directedAffineCover.pullback₁ X.hom)).toOver Y
    (fun U ↦ (Y.directedAffineCover.pullback₁ X.hom).f U ≫ X.hom) fun g ↦ by
      rw [Cover.functorOfLocallyDirected_map, ← Category.assoc, Cover.trans_map]

/-- A `Y`-scheme is determined up to isomorphism by its restrictions to the affine opens of
`Y`. -/
theorem nonempty_iso_of_restrictAffineOpens_iso {X X' : Over Y}
    (e : restrictAffineOpens X ≅ restrictAffineOpens X') : Nonempty (X ≅ X') := by
  let 𝒰 := Y.directedAffineCover.pullback₁ X.hom
  let 𝒰' := Y.directedAffineCover.pullback₁ X'.hom
  let e' : Cover.functorOfLocallyDirected 𝒰 ≅ Cover.functorOfLocallyDirected 𝒰' :=
    Functor.isoWhiskerRight e (Over.forget Y)
  let φ : X.left ≅ X'.left := IsColimit.coconePointsIsoOfNatIso
    (OpenCover.isColimitCoconeOfLocallyDirected 𝒰)
    (OpenCover.isColimitCoconeOfLocallyDirected 𝒰') e'
  refine ⟨Over.isoMk φ ?_⟩
  refine Cover.hom_ext 𝒰 _ _ fun U ↦ ?_
  have h₁ : 𝒰.f U ≫ φ.hom = e'.hom.app U ≫ 𝒰'.f U :=
    IsColimit.comp_coconePointsIsoOfNatIso_hom (OpenCover.isColimitCoconeOfLocallyDirected 𝒰)
      (OpenCover.isColimitCoconeOfLocallyDirected 𝒰') e' U
  have h₂ := Over.w (e.hom.app U)
  rw [← Category.assoc, h₁, Category.assoc]
  exact h₂

/-- The `Y`-schemes which are affine and locally of finite type over `Y`. -/
def isAffineHomLocallyOfFiniteType : ObjectProperty (Over Y) :=
  fun X ↦ IsAffineHom X.hom ∧ LocallyOfFiniteType X.hom

/-- The `Y`-schemes whose source is affine and which are locally of finite type over `Y`. -/
def isAffineLocallyOfFiniteType : ObjectProperty (Over Y) :=
  fun X ↦ IsAffine X.left ∧ LocallyOfFiniteType X.hom

instance : ObjectProperty.EssentiallySmall.{u} (isAffineLocallyOfFiniteType (Y := Y)) := by
  have := essentiallySmall_costructuredArrow_Spec (X := Y) @LocallyOfFiniteType le_rfl
  let F := MorphismProperty.CostructuredArrow.forget @LocallyOfFiniteType ⊤ Scheme.Spec Y ⋙
    CostructuredArrow.toOver Scheme.Spec Y
  refine ObjectProperty.EssentiallySmall.of_le (Q := F.essImage) fun X ⟨hX, hf⟩ ↦ ?_
  refine ⟨MorphismProperty.CostructuredArrow.mk ⊤ (A := Opposite.op Γ(X.left, ⊤))
    (X.left.isoSpec.inv ≫ X.hom)
      ((MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType _ _).2 hf),
    ⟨Over.isoMk X.left.isoSpec.symm⟩⟩

instance : LocallySmall.{u} (isAffineLocallyOfFiniteType (Y := Y)).FullSubcategory where
  hom_small _ _ := inferInstance

/-- The restriction of a `Y`-scheme affine and locally of finite type over `Y` to an affine open
of `Y` is affine and locally of finite type over `Y`. -/
lemma isAffineLocallyOfFiniteType_restrictAffineOpens_obj {X : Over Y}
    (hX : isAffineHomLocallyOfFiniteType X) (U : Y.affineOpens) :
    isAffineLocallyOfFiniteType ((restrictAffineOpens X).obj U) := by
  obtain ⟨_, _⟩ := hX
  have : IsAffine U.1.toScheme := U.2
  refine ⟨?_, ?_⟩
  · have : IsAffineHom (pullback.snd X.hom U.1.ι) :=
      MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ ‹_›
    exact isAffine_of_isAffineHom (pullback.snd X.hom U.1.ι)
  · exact inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom U.1.ι ≫ X.hom))

/-- **`Y`-schemes affine and locally of finite type over `Y` form an essentially small
family.** -/
theorem small_skeleton_isAffineHomLocallyOfFiniteType :
    Small.{u} (Skeleton (isAffineHomLocallyOfFiniteType (Y := Y)).FullSubcategory) := by
  let D := (isAffineLocallyOfFiniteType (Y := Y)).FullSubcategory
  have : EssentiallySmall.{u} (Y.affineOpens ⥤ D) := by
    rw [essentiallySmall_congr ((equivSmallModel.{u} D).congrRight (E := Y.affineOpens))]
    exact EssentiallySmall.mk' (CategoryTheory.Equivalence.refl)
  let H (X : (isAffineHomLocallyOfFiniteType (Y := Y)).FullSubcategory) : Y.affineOpens ⥤ D :=
    ObjectProperty.lift _ (restrictAffineOpens X.obj)
      (isAffineLocallyOfFiniteType_restrictAffineOpens_obj X.property)
  let g : Skeleton (isAffineHomLocallyOfFiniteType (Y := Y)).FullSubcategory →
      Skeleton (Y.affineOpens ⥤ D) := fun x ↦ toSkeleton (H (Quotient.out x))
  refine small_of_injective (f := g) fun x y hxy ↦ ?_
  obtain ⟨e⟩ : Nonempty (H (Quotient.out x) ≅ H (Quotient.out y)) := Quotient.exact hxy
  obtain ⟨e'⟩ := nonempty_iso_of_restrictAffineOpens_iso
    (Functor.isoWhiskerRight e (ObjectProperty.ι _))
  rw [← Quotient.out_eq x, ← Quotient.out_eq y]
  exact Quotient.sound ⟨ObjectProperty.isoMk _ e'⟩

end AlgebraicGeometry.Scheme.Over
