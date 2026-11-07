/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplexClassesSmallOnOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.PerfectGluingEndpointsSmall
import WeilConjectures.AlgebraicGeometry.PerfectGluingTrianglePresentation
public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

universe u w

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Pretriangulated in
private theorem small_skeleton_of_triangle_terms
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{u} C]
    {D : Type*} [Category D] (F : D ⥤ C) [F.Full] [F.Faithful]
    (P Q : ObjectProperty C)
    [Small.{u} (Skeleton P.FullSubcategory)]
    [Small.{u} (Skeleton Q.FullSubcategory)]
    (h : ∀ X : D, ∃ T : Triangle C, T ∈ distTriang C ∧
      P T.obj₂ ∧ Q T.obj₃ ∧ Nonempty (T.obj₁ ≅ F.obj X)) :
    Small.{u} (Skeleton D) := by
  classical
  let A := Skeleton P.FullSubcategory
  let B := Skeleton Q.FullSubcategory
  let a (s : A) := ((fromSkeleton P.FullSubcategory).obj s).obj
  let b (t : B) := ((fromSkeleton Q.FullSubcategory).obj t).obj
  let I := Σ s : A, Σ t : B, (a s ⟶ b t)
  let f : I → Skeleton (Arrow C) := fun i ↦ toSkeleton (Arrow.mk i.2.2)
  have h' (s : Skeleton D) := h ((fromSkeleton D).obj s)
  choose T hT hP hQ he using h'
  let e (s : Skeleton D) := Classical.choice (he s)
  let g : Skeleton D → Skeleton (Arrow C) := fun s ↦ toSkeleton (Arrow.mk (T s).mor₂)
  have hmem (s : Skeleton D) : g s ∈ Set.range f := by
    let A₀ : P.FullSubcategory := ⟨(T s).obj₂, hP s⟩
    let B₀ : Q.FullSubcategory := ⟨(T s).obj₃, hQ s⟩
    let ea := P.ι.mapIso (fromSkeletonToSkeletonIso A₀)
    let eb := Q.ι.mapIso (fromSkeletonToSkeletonIso B₀)
    refine ⟨⟨toSkeleton A₀, toSkeleton B₀, ea.hom ≫ (T s).mor₂ ≫ eb.inv⟩, ?_⟩
    apply congr_toSkeleton_of_iso
    exact Arrow.isoMk ea eb (by simp)
  let g' : Skeleton D → Set.range f := fun s ↦ ⟨g s, hmem s⟩
  apply small_of_injective (f := g')
  intro s t hst
  have hab : g s = g t := congrArg Subtype.val hst
  obtain ⟨eab⟩ := toSkeleton_eq_toSkeleton_iff.mp hab
  obtain ⟨et, _, _⟩ := exists_iso_of_arrow_iso (T s).rotate (T t).rotate
    (rot_of_distTriang _ (hT s)) (rot_of_distTriang _ (hT t)) eab
  let ex : F.obj ((fromSkeleton D).obj s) ≅ F.obj ((fromSkeleton D).obj t) :=
    (e s).symm ≪≫ (shiftFunctor C (1 : ℤ)).preimageIso (Triangle.π₃.mapIso et) ≪≫ e t
  simpa only [toSkeleton_fromSkeleton_obj] using
    congr_toSkeleton_of_iso (F.preimageIso ex)

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
