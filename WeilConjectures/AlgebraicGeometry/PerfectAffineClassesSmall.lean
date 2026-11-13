/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Small.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.PerfectAffineFinitePresentation
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall

/-! # Smallness of perfect isomorphism classes on an affine scheme

## References

* Stacks Project, Tag 08EB.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Small encoding of a complex with finitely generated terms. -/
private structure FiniteTermModel (A : Type u) [CommRing A] : Type u where
  X : ℤ → FGModuleRepr A
  d : ∀ i j : ℤ, ModuleCat.of A (X i) ⟶ ModuleCat.of A (X j)
  shape : ∀ i j : ℤ, ¬(ComplexShape.up ℤ).Rel i j → d i j = 0
  square : ∀ i j k : ℤ, d i j ≫ d j k = 0

private def FiniteTermModel.complex {A : Type u} [CommRing A] (M : FiniteTermModel A) :
    CochainComplex (ModuleCat.{u} A) ℤ where
  X i := ModuleCat.of A (M.X i)
  d := M.d
  shape := M.shape
  d_comp_d' i j k _ _ := M.square i j k

private theorem exists_finiteTermModel {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : ∀ n, Module.Finite A (P.X n)) :
    ∃ M : FiniteTermModel A, Nonempty (M.complex ≅ P) := by
  classical
  let X (n : ℤ) : FGModuleRepr A := by
    have := hP n
    exact FGModuleRepr.ofFinite A (P.X n)
  let e (n : ℤ) : ModuleCat.of A (X n) ≅ P.X n := by
    have := hP n
    exact (FGModuleRepr.ofFiniteEquiv A (P.X n)).toModuleIso
  let M : FiniteTermModel A :=
    { X := X
      d i j := (e i).hom ≫ P.d i j ≫ (e j).inv
      shape i j h := by rw [P.shape i j h]; simp
      square i j k := by simp [Category.assoc] }
  refine ⟨M, ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩⟩
  intro i j _
  change (e i).hom ≫ P.d i j = ((e i).hom ≫ P.d i j ≫ (e j).inv) ≫ (e j).hom
  simp

/-- Perfect quasi-coherent derived objects on an affine scheme have `u`-small
isomorphism classes (Stacks, Tag 08EB). -/
theorem small_perfectComplex_classes_of_isAffine (Y : Scheme.{u}) [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))] :
    Small.{u} (Skeleton (ObjectProperty.FullSubcategory
      (fun E : schemeDerivedQCohCategory Y ↦ IsPerfect Y E.obj))) := by
  classical
  let Q : ObjectProperty (schemeDerivedQCohCategory Y) := fun E ↦ IsPerfect Y E.obj
  let F := affineModuleComplexFunctor Y ⋙ DerivedCategory.Q
  let f : FiniteTermModel Γ(Y, ⊤) → Skeleton (schemeDerivedCategory Y) :=
    fun M ↦ toSkeleton (F.obj M.complex)
  let inclusion : Q.FullSubcategory ⥤ schemeDerivedCategory Y :=
    Q.ι ⋙ (schemeDerivedQCohProperty Y).ι
  have hmem (E : Q.FullSubcategory) : toSkeleton (inclusion.obj E) ∈ Set.range f := by
    obtain ⟨P, hP, ⟨eP⟩⟩ := exists_affine_finite_module_presentation Y E.obj E.property
    obtain ⟨M, ⟨eM⟩⟩ := exists_finiteTermModel P hP
    refine ⟨M, ?_⟩
    exact congr_toSkeleton_of_iso ((F.mapIso eM) ≪≫ eP.symm)
  let g : Skeleton Q.FullSubcategory → Set.range f := fun s ↦
    ⟨inclusion.mapSkeleton.obj s, by
      rw [← toSkeleton_fromSkeleton_obj s, Functor.mapSkeleton_obj_toSkeleton]
      exact hmem ((fromSkeleton Q.FullSubcategory).obj s)⟩
  apply small_of_injective (f := g)
  intro s t h
  exact inclusion.mapSkeleton_injective (congrArg Subtype.val h)

end AlgebraicGeometry.Scheme
