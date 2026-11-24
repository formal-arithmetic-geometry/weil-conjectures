/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelsExist
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementPairingForModels

/-! # Multiplicative Godement models -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Construct the multiplicative cosimplicial Godement model, before establishing
flasqueness or exactness (Stacks, Tag 0FKR; Banerjee, §1.1.4). -/
theorem moduleCup_godement_model_pairing (X : Scheme.{u}) (F G : X.Modules) :
    ∃ (A B C : CosimplicialObject X.Modules)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
        (((alternatingCofaceMapComplex X.Modules).obj A).extend
          ComplexShape.embeddingUpNat))
      (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
        (((alternatingCofaceMapComplex X.Modules).obj B).extend
          ComplexShape.embeddingUpNat))
      (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶
        (((alternatingCofaceMapComplex X.Modules).obj C).extend
          ComplexShape.embeddingUpNat))
      (μ : CategoryTheory.Monoidal.FunctorCategory.tensorObj
        (C := SimplexCategory) (D := X.Modules) A B ⟶ C),
      ModuleCupGodementModel X F A a ∧ ModuleCupGodementModel X G B b ∧
      ModuleCupGodementModel X (F ⊗ G) C c ∧
      ∀ (V : X.Opens)
        (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F).X 0, V))
        (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G).X 0, V)),
        (((((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).hom ⊗ₘ
          (((alternatingCofaceMapComplex X.Modules).obj B).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).hom) ≫ μ.app ⦋0⦌ ≫
          (((alternatingCofaceMapComplex X.Modules).obj C).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).inv).val.app (op V)
          (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y)) =
        (c.f 0).val.app (op V) (tmulSection x y) := by
  obtain ⟨A, a, hA, sA⟩ := moduleCup_godement_models_exist X F
  obtain ⟨B, b, hB, sB⟩ := moduleCup_godement_models_exist X G
  obtain ⟨C, c, hC, sC⟩ := moduleCup_godement_models_exist X (F ⊗ G)
  obtain ⟨μ, hμ⟩ :=
    moduleCup_godement_pairing_for_models X F G A B C a b c hA hB hC sA sB sC
  refine ⟨A, B, C, a, b, c, μ, hA, hB, hC, ?_⟩
  intro V x y
  have h := congrArg (fun f ↦ f.app V (tmulSection x y)) hμ
  rw [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection] at h
  exact h

end
end AlgebraicGeometry.Scheme.Modules
