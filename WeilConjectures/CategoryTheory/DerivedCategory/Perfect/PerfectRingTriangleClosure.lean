/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Perfect ring complexes are closed under triangle extensions

Source: Stacks Project, More on Algebra, Tag 066R,
the first-and-third-imply-second case.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Pretriangulated

namespace DerivedCategory

-- These helpers adapt the bounded-model proofs in
-- WeilConjectures.CategoryTheory.DerivedCategory.Perfect to an independent universe w.
private theorem perfectRing_of_iso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {C D : DerivedCategory (ModuleCat.{u} R)}
    (hC : IsPerfectRingComplex C)
    (e : C ≅ D) : IsPerfectRingComplex D := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e'⟩⟩ := hC
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ e'⟩⟩

private lemma perfectRing_Q_obj {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ)
    [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hP : ∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) :
    IsPerfectRingComplex (Q.obj P) :=
  ⟨P, a, b, inferInstance, inferInstance, hP, ⟨Iso.refl _⟩⟩

/-- Perfect complexes are stable under shifts. -/
private lemma perfectRing_shift {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : IsPerfectRingComplex C) (n : ℤ) :
    IsPerfectRingComplex (C⟦n⟧) := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := hC
  have := P.isStrictlyGE_shift a n (a - n) (by omega)
  have := P.isStrictlyLE_shift b n (b - n) (by omega)
  exact perfectRing_of_iso
    (perfectRing_Q_obj (P⟦n⟧) (a - n) (b - n) fun i ↦ hP (i + n))
    (((Q.commShiftIso n).app P) ≪≫ (shiftFunctor _ n).mapIso e.symm)

/-- The mapping cone of a morphism between bounded complexes of finitely generated projective
modules is again such a complex. -/
private lemma perfectRing_Q_obj_mappingCone {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {P₁ P₂ : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P₁ ⟶ P₂)
    (a₁ b₁ a₂ b₂ : ℤ) [P₁.IsStrictlyGE a₁] [P₁.IsStrictlyLE b₁] [P₂.IsStrictlyGE a₂]
    [P₂.IsStrictlyLE b₂] (h₁ : ∀ i, Module.Projective R (P₁.X i) ∧ Module.Finite R (P₁.X i))
    (h₂ : ∀ i, Module.Projective R (P₂.X i) ∧ Module.Finite R (P₂.X i)) :
    IsPerfectRingComplex (Q.obj (CochainComplex.mappingCone φ)) := by
  have : (CochainComplex.mappingCone φ).IsStrictlyGE (min (a₁ - 1) a₂) :=
    CochainComplex.isStrictlyGE_mappingCone φ a₁ a₂ _
  have : (CochainComplex.mappingCone φ).IsStrictlyLE (max (b₁ - 1) b₂) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P₁.isZero_of_isStrictlyLE b₁ _ (by omega), P₂.isZero_of_isStrictlyLE b₂ _ (by omega)⟩
  refine perfectRing_Q_obj _ (min (a₁ - 1) a₂) (max (b₁ - 1) b₂) fun i ↦ ?_
  let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl) ≪≫
    ModuleCat.biprodIsoProd (P₁.X (i + 1)) (P₂.X i)
  have := (h₁ (i + 1)).1
  have := (h₁ (i + 1)).2
  have := (h₂ i).1
  have := (h₂ i).2
  exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
    Module.Finite.equiv e.toLinearEquiv.symm⟩

/-- In a distinguished triangle over a commutative ring, perfect first and third objects
imply a perfect second object, in any chosen localization universe.
Source: Stacks Project, More on Algebra, Tag 066R. -/
theorem isPerfectRingComplex_obj₂_of_distTriang {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)))
    (h₁ : IsPerfectRingComplex T.obj₁) (h₃ : IsPerfectRingComplex T.obj₃) :
    IsPerfectRingComplex T.obj₂ := by
  obtain ⟨P₁, a₁, b₁, _, _, hP₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨P₃, a₃, b₃, _, _, hP₃, ⟨e₃⟩⟩ := h₃
  have : ∀ n, Projective (P₃.X n) := fun n ↦ by
    have := (hP₃ n).1
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : P₃.IsKProjective := CochainComplex.isKProjective_of_projective _ b₃
  have := P₁.isStrictlyGE_shift a₁ 1 (a₁ - 1) (by omega)
  have := P₁.isStrictlyLE_shift b₁ 1 (b₁ - 1) (by omega)
  obtain ⟨ψ, hψ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P₃ (P₁⟦(1 : ℤ)⟧)
    (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).inv)
  have hcomm : Q.map ψ ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).hom ≫ e₁.inv⟦(1 : ℤ)⟧' =
      e₃.inv ≫ T.mor₃ := by
    rw [hψ]
    simp [← Functor.map_comp]
  obtain ⟨f, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _
    (mappingCone_triangle_distinguished ψ)
    (Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang _ hT))
    (Arrow.isoMk e₃.symm (((Q.commShiftIso (1 : ℤ)).app P₁) ≪≫ (shiftFunctor _ 1).mapIso e₁.symm)
      hcomm.symm)
  have hcone := perfectRing_Q_obj_mappingCone ψ a₃ b₃ (a₁ - 1) (b₁ - 1) hP₃ fun i ↦ hP₁ (i + 1)
  exact perfectRing_of_iso
    (perfectRing_shift (perfectRing_of_iso hcone (Triangle.π₃.mapIso f)) (-1))
    ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app _)

end DerivedCategory
