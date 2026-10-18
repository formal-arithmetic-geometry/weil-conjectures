/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Injective resolutions along exact functors preserving injective objects

An exact functor `F : C ⥤ D` preserving injective objects sends an injective resolution of `Z`
to an injective resolution of `F Z` (`CategoryTheory.InjectiveResolution.map`).
-/

@[expose] public section

namespace CategoryTheory.InjectiveResolution

open Limits

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (F : C ⥤ D)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects]

/-- The image of an injective resolution under an exact functor preserving injective objects. -/
@[simps]
noncomputable def map {Z : C} (R : InjectiveResolution Z) : InjectiveResolution (F.obj Z) where
  cocomplex := (F.mapHomologicalComplex _).obj R.cocomplex
  injective n := F.injective_obj (R.cocomplex.X n)
  ι := ((HomologicalComplex.singleMapHomologicalComplex F _ 0).app Z).inv ≫
    (F.mapHomologicalComplex _).map R.ι
  quasiIso := inferInstance

lemma map_cocomplex_d {Z : C} (R : InjectiveResolution Z) (i j : ℕ) :
    (R.map F).cocomplex.d i j = F.map (R.cocomplex.d i j) :=
  rfl

variable {F} in
/-- A natural endomorphism `τ` of `F` induces an endomorphism of the image `F(R)` of an injective
resolution `R` of `Z`, over `τ_Z`. -/
@[simps]
noncomputable def mapHomOfNatTrans (τ : F ⟶ F) {Z : C} (R : InjectiveResolution Z) :
    InjectiveResolution.Hom (R.map F) (R.map F) (τ.app Z) where
  hom := (NatTrans.mapHomologicalComplex τ _).app R.cocomplex
  ι_f_zero_comp_hom_f_zero := by
    simp [HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single_map_f_self]

namespace Hom

variable {Z Z' Z'' : C} {I : InjectiveResolution Z} {I' : InjectiveResolution Z'}
  {I'' : InjectiveResolution Z''}

/-- The composite of morphisms of injective resolutions. -/
@[simps]
def comp {f : Z ⟶ Z'} {g : Z' ⟶ Z''} (φ : Hom I I' f) (ψ : Hom I' I'' g) : Hom I I'' (f ≫ g) where
  hom := φ.hom ≫ ψ.hom
  ι_f_zero_comp_hom_f_zero := by simp

/-- A morphism of injective resolutions over `f`, as one over `f' = f`. -/
@[simps]
def ofEq {f f' : Z ⟶ Z'} (φ : Hom I I' f) (h : f = f') : Hom I I' f' where
  hom := φ.hom
  ι_f_zero_comp_hom_f_zero := by rw [φ.ι_f_zero_comp_hom_f_zero, h]

/-- The image of a morphism of injective resolutions under an exact functor preserving injective
objects. -/
@[simps]
noncomputable def map {f : Z ⟶ Z'} (φ : Hom I I' f) : Hom (I.map F) (I'.map F) (F.map f) where
  hom := (F.mapHomologicalComplex _).map φ.hom
  ι_f_zero_comp_hom_f_zero := by
    have h₁ := HomologicalComplex.congr_hom
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.naturality f) 0
    have h₂ := congrArg F.map φ.ι_f_zero_comp_hom_f_zero
    simp only [Functor.map_comp] at h₂
    simp only [map_ι, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Category.assoc,
      Functor.comp_map] at h₁ ⊢
    rw [← Functor.map_comp, φ.ι_f_zero_comp_hom_f_zero, Functor.map_comp, ← Category.assoc,
      ← Category.assoc]
    congr 1
    exact h₁.symm

end Hom

/-- The descent of a morphism `f : Z ⟶ Z'` to injective resolutions, as a morphism of injective
resolutions. -/
@[simps]
noncomputable def descHom {Z Z' : C} (f : Z ⟶ Z') (I : InjectiveResolution Z)
    (I' : InjectiveResolution Z') : Hom I I' f where
  hom := desc f I' I
  ι_f_zero_comp_hom_f_zero := by simp

end CategoryTheory.InjectiveResolution
