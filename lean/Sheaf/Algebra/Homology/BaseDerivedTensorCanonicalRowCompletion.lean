/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.ExactSequence
import Sheaf.Algebra.Homology.BaseDerivedExtensionCoherentTriangle

/-! # Canonical completion of the derived tensor row

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

set_option linter.unusedSectionVars false in
private theorem tensorLinearLift
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (M N : ModuleCat.{u} (A ⊗[R] B))
    (f : (restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj M ⟶
      (restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj N)
    (h : ∀ (a : A) (x : M),
      f ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • f x) :
    ∃ g : M ⟶ N,
      (restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g = f := by
  refine ⟨ofHom { toFun := f, map_add' := f.hom.map_add, map_smul' := ?_ }, ?_⟩
  · intro e x
    change f (e • x) = e • f x
    induction e using TensorProduct.induction_on with
    | zero => simpa only [RingHom.id_apply, zero_smul] using f.hom.map_zero
    | tmul a b =>
      have hb (y : M) :
          f ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) • y) =
            (Algebra.TensorProduct.includeRight b : A ⊗[R] B) • f y :=
        f.hom.map_smul b y
      have he : (a ⊗ₜ[R] b : A ⊗[R] B) =
          (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) *
            Algebra.TensorProduct.includeRight b := by
        simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [he, mul_smul, h, hb, mul_smul]
    | add e e' he he' =>
      simpa only [add_smul, RingHom.id_apply] using (f.hom.map_add (e • x) (e' • x)).trans
        (congrArg₂ (· + ·) he he')
  · ext x
    rfl


set_option backward.isDefEq.respectTransparency false in
private theorem map_to_common_derived
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
    (m : BaseDerivedTensorCohomologyModel R A B Q C)
    (n : BaseDerivedTensorCohomologyModel R A B Q' C) (i : ℤ)
    (δ : m.derived ⟶ n.derived) (g : m.cohomology i ⟶ n.cohomology i)
    (hδ : Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
      n.counit = m.counit)
    (hg : (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
          (n.cohomologyIso i).hom =
      (m.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (m.derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map f)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (δ.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q'))))) :
    let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
    let F := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
      HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let cm := Functor.leftDerivedNatTrans m.derived L m.counit ε W (𝟙 _)
    let cn := Functor.leftDerivedNatTrans n.derived L n.counit ε W (𝟙 _)
    (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map g ≫
        (n.cohomologyIso i).hom ≫ H.map (cn.app (F.obj Q')) =
      (m.cohomologyIso i).hom ≫ H.map (cm.app (F.obj Q)) ≫ H.map (L.map (F.map f)) := by
  intro W F H cm cn
  have hc : δ ≫ cn = cm := by
    apply Functor.leftDerived_ext L ε W m.derived
    simp only [Functor.whiskerLeft_comp, Category.assoc]
    rw [Functor.leftDerivedNatTrans_fac, Category.comp_id, hδ,
      Functor.leftDerivedNatTrans_fac, Category.comp_id]
  rw [← Category.assoc, hg]
  simp only [Category.assoc]
  change (m.cohomologyIso i).hom ≫ H.map (m.derived.map (F.map f)) ≫
    H.map (δ.app (F.obj Q')) ≫ H.map (cn.app (F.obj Q')) = _
  rw [← H.map_comp (δ.app _) (cn.app _), ← NatTrans.comp_app, hc]
  rw [← H.map_comp, cm.naturality, H.map_comp]
  rfl

/-- Complete the canonical same-degree model maps by the derived connecting map.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, exactness and independence of
choices; step 1 of lem-pc-base-derived-tensor-ordinary-triangle-rows.

Proof: choose the triangulated universal derived extension supplied by
exists_baseDerivedExtension_resolution. Universal uniqueness identifies it with
m₁.derived. The coherent shift compatible with the counit is unique by the right
Kan universal property, so this identification respects the given shift structure.
Exact restriction A to R sends the localized distinguished triangle to D(R).
Apply derived extension and its long exact cohomology sequence. Identify all
three vertices with the prescribed model cohomology via universal counit
uniqueness. The hypotheses hg0, hg1 and hg3 identify its three same-degree maps
with the prescribed s₀, s₁ and s₃: the counit identities force each δk to be the
unique universal transformation. Define the B-linear boundary by the displayed
formula. Multiplication by a in A defines an endomorphism of the input triangle;
naturality of the cohomology connecting map, the cohomologyIso_smul identities
and naturality of the unique universal comparison show that this B-linear map
commutes with a tensor 1. It already commutes with 1 tensor b by B-linearity.
Tensor induction gives E-linearity, E = A tensor_R B, and thus a morphism s₂.
Its restriction is exactly the stated formula by construction. The B-linear
row is conjugate to the long exact row; exact faithful restriction E to B
reflects exactness, proving the first conclusion. No ordinary counit comparison
square is claimed here. Zero rings, zero complexes and arbitrary degrees use
the same universal-property and tensor-induction arguments.
(blueprint: lem-pc-base-derived-tensor-canonical-row-completion). -/
theorem exists_baseDerivedTensor_canonical_row_completion
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    [HasDerivedCategory (ModuleCat.{u} A)]
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles)
    (m₁ : BaseDerivedTensorCohomologyModel R A B T.obj₁ C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B T.obj₃ C)
    [m₁.derived.CommShift ℤ] [NatTrans.CommShift m₁.counit ℤ]
    (m₂ : BaseDerivedTensorCohomologyModel R A B T.obj₂ C) (i : ℤ)
    (δ0 : m₁.derived ⟶ m₂.derived) (δ1 : m₂.derived ⟶ m₃.derived)
    (δ3 : m₁.derived ⟶ m₂.derived)
    (s0 : m₁.cohomology i ⟶ m₂.cohomology i)
    (s1 : m₂.cohomology i ⟶ m₃.cohomology i)
    (s3 : m₁.cohomology (i + 1) ⟶ m₂.cohomology (i + 1))
    (hδ0 : Functor.whiskerLeft DerivedCategory.Qh δ0 ≫ m₂.counit = m₁.counit)
    (hδ1 : Functor.whiskerLeft DerivedCategory.Qh δ1 ≫ m₃.counit = m₂.counit)
    (hδ3 : Functor.whiskerLeft DerivedCategory.Qh δ3 ≫ m₂.counit = m₁.counit)
    (hg0 : (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map s0 ≫
          (m₂.cohomologyIso i).hom =
      (m₁.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (m₁.derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map
                T.mor₁)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (δ0.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
                T.obj₂)))))
    (hg1 : (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map s1 ≫
          (m₃.cohomologyIso i).hom =
      (m₂.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (m₂.derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map
                T.mor₂)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (δ1.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
                T.obj₃)))))
    (hg3 : (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map s3 ≫
          (m₂.cohomologyIso (i + 1)).hom =
      (m₁.cohomologyIso (i + 1)).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (i + 1)).map
          (m₁.derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map
                T.mor₁)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (i + 1)).map
          (δ3.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
                T.obj₂))))) :
    letI := m₁.universal
    let δ := Functor.leftDerivedNatTrans m₃.derived m₁.derived m₃.counit m₁.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (𝟙 _)
    let D := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
      HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ m₁.derived
    let X := DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
      (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
                T.obj₃))
    ∃ s₂ : m₃.cohomology i ⟶ m₁.cohomology (i + 1),
      (ComposableArrows.mk₄ s0 s1 s₂ s3).Exact ∧
      (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map s₂ ≫
        (m₁.cohomologyIso (i + 1)).hom =
      (m₃.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map (δ.app X) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).shiftMap
          (ShiftedHom.map T.mor₃ D) i (i + 1) (by omega) := by sorry
end ModuleCat
