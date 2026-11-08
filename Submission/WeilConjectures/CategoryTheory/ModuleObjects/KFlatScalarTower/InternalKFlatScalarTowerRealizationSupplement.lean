/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

import Submission.WeilConjectures.Algebra.Homology.BifunctorSingleNaturality
import Submission.WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import Submission.WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealization

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Realizing a scalar tower on native K-flat internal modules

This is the internal-module counterpart of the scalar realization in
`lem-pe-kflat-scalar-tower-realization`. It concerns individual scalar extensions,
their transitions and units; it involves neither products nor inverse limits.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod.KFlatScalarTower

section Computation
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
private def extendTensorIso (M : Mod C R) :
    (Mod.comap φ).obj ((Mod.extendScalars φ).obj M) ≅
      (Mod.comap φ).obj (Mod.regular S) ⊗ M := by
  let e := Mod.extendForgetTensorObjIso φ M
  have hπ : Mod.extendπ φ M ≫ e.hom =
      Mod.tensorObjπ ((Mod.comap φ).obj (Mod.regular S)) M := by
    simp [e, Mod.extendForgetTensorObjIso]
  refine Mod.isoMk e ?_
  rw [← cancel_epi (R ◁ Mod.extendπ φ M)]
  change R ◁ Mod.extendπ φ M ≫
    γ[R,((Mod.comap φ).obj (Mod.extendScalarsObj φ M)).X] ≫ e.hom =
      R ◁ Mod.extendπ φ M ≫ R ◁ e.hom ≫
        γ[R,((Mod.comap φ).obj (Mod.regular S) ⊗ M).X]
  rw [Mod.comap_obj_smul, Category.assoc, whisker_exchange_assoc,
    Mod.whiskerLeft_extendπ_smul_assoc, associator_inv_naturality_left_assoc,
    hπ, ← whiskerLeft_comp_assoc, hπ, Mod.whiskerLeft_tensorπ_smul,
    Mod.comap_obj_smul, comp_whiskerRight]
  simp only [Category.assoc]
  rfl

private def extendTensorNatIso :
    Mod.extendScalars φ ⋙ Mod.comap φ ≅
      tensorLeft ((Mod.comap φ).obj (Mod.regular S)) :=
  NatIso.ofComponents (extendTensorIso φ) (by
    intro M N f
    apply Mod.hom_ext
    simpa [extendTensorIso, Mod.extendForgetTensorIso] using
      (Mod.extendForgetTensorIso φ).hom.naturality f)

private def computationCounit :
    DerivedCategory.Q ⋙ (Mod.extendScalars φ).leftDerivedFunctor ⟶
      (Mod.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let E := Mod.extendScalars φ
  let q := HomotopyCategory.quotient (Mod C R) (.up ℤ)
  let j : q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (Mod C S))
  exact Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Mod C R)).inv
      E.leftDerivedFunctor ≫ Functor.whiskerLeft q E.leftDerivedFunctorCounit ≫ j.hom

variable {T : C} [MonObj T] [IsCommMonObj T]
  (ψ : S ⟶ T) [IsMonHom ψ] (χ : R ⟶ T) [IsMonHom χ]
  (h : φ ≫ ψ = χ)

private def extendTensorRightNatIso :
    Mod.extendScalars φ ⋙ Mod.comap φ ≅
      tensorRight ((Mod.comap φ).obj (Mod.regular S)) :=
  extendTensorNatIso φ ≪≫
    BraidedCategory.tensorLeftIsoTensorRight ((Mod.comap φ).obj (Mod.regular S))

end Computation

attribute [local irreducible] extendTensorIso extendTensorNatIso extendTensorRightNatIso

section TensorTransport
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C]

end TensorTransport

section StepNaturality
end StepNaturality

section RepresentativeTransport
end RepresentativeTransport

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  (R : C) [MonObj R] [IsCommMonObj R]
  (S : ℕ → C) [∀ n, MonObj (S n)] [∀ n, IsCommMonObj (S n)]
  (q : ∀ n, R ⟶ S n) [∀ n, IsMonHom (q n)]
  (r : ∀ n, S (n + 1) ⟶ S n) [∀ n, IsMonHom (r n)]
  (h : ∀ n, q (n + 1) ≫ r n = q n)

variable (B : ℕ → Mod C R) (ι : ∀ n, 𝟙_ (Mod C R) ⟶ B n)
  (τ : ∀ n, B (n + 1) ⟶ B n)


section
set_option backward.defeqAttrib.useBackward true

namespace PrincipalTensorAux

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [IsGrothendieckAbelian.{v} A] [Abelian.HasFunctorialFlatResolution A]

private abbrev single (B : A) := (HomologicalComplex.single A (.up ℤ) 0).obj B

private def tensorComparison (B : A) :
    DerivedCategory.Q ⋙ tensorRight ((DerivedCategory.singleFunctor A 0).obj B) ⟶
      (tensorRight B).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := Functor.LaxMonoidal.μ DerivedCategory.Q P (single B) ≫
    DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) B P).hom
  naturality P P' f := by
    dsimp only [Functor.comp_map]
    change (DerivedCategory.Q.map f ▷ DerivedCategory.Q.obj (single B)) ≫ _ = _
    rw [← Category.assoc, Functor.LaxMonoidal.μ_natural_left]
    simp only [Category.assoc]
    have ht := CochainComplex.mapBifunctorSingle₂Iso_hom_naturality (curriedTensor A) B f
    have ht' : f ▷ single B ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) B P').hom =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) B P).hom ≫
        ((tensorRight B).mapHomologicalComplex (.up ℤ)).map f := ht
    rw [← DerivedCategory.Q.map_comp, ht', DerivedCategory.Q.map_comp]

end PrincipalTensorAux

end

end CategoryTheory.Mod.KFlatScalarTower
