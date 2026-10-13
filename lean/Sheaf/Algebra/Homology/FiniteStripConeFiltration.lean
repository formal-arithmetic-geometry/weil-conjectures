/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-! # Vertical filtration of a finite-strip augmentation cone

Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

/-- (blueprint: lem-sc-finite-strip-cone-filtration-steps)
Proof: construct the finite joins of source and target image subobjects, verify
stability under the cone differential, and use the support bounds to obtain the
two endpoint identities. -/
theorem finite_strip_cone_filtration_steps
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p) :
    ∃ F : DecreasingFiltration (CochainComplex.mappingCone b),
      (∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
          if p ≤ n - i then imageSubobject
            (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
              (CochainComplex.mappingCone.inr b).f n) else ⊥)) ∧
      (∀ n : ℤ, F.complexStep (n - (r : ℤ)) n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) := by sorry

/-- (blueprint: lem-sc-finite-strip-cone-filtration-graded)
Proof: quotient successive filtration steps, identify the surviving diagonal
with the translated row cone, and transport the resulting short-complex
homology isomorphism. -/
theorem finite_strip_cone_filtration_graded
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥)) :
      ∀ p n : ℤ, Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone (f p)).homology (n - p)) := by sorry

theorem finite_strip_cone_filtration
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p) :
    ∃ F : DecreasingFiltration (CochainComplex.mappingCone b),
      (∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
          if p ≤ n - i then imageSubobject
            (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
              (CochainComplex.mappingCone.inr b).f n) else ⊥)) ∧
      (∀ n : ℤ, F.complexStep (n - (r : ℤ)) n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) ∧
      (∀ p n : ℤ, Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone (f p)).homology (n - p))) := by
  obtain ⟨F, hF, hbound⟩ := finite_strip_cone_filtration_steps K r hsupport A a b hb f hf
  exact ⟨F, hF, hbound, finite_strip_cone_filtration_graded K r hsupport A a b hb f hf F hF⟩

end HomologicalComplex₂
