/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupResolutionData
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelPairing
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelQuasiIso
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementObjectFlasque
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Cosimplicial input for the Godement cup product -/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section


/-- Extend the unnormalized alternating coface complex by zero in negative degrees. -/
def moduleCup_cosimplicialComplex (X : Scheme.{u}) (A : CosimplicialObject X.Modules) :
    CochainComplex X.Modules ℤ :=
  ((alternatingCofaceMapComplex X.Modules).obj A).extend ComplexShape.embeddingUpNat

/-- The degree-zero identification with the cosimplicial term. -/
def moduleCup_cosimplicialZeroIso (X : Scheme.{u}) (A : CosimplicialObject X.Modules) :
    (moduleCup_cosimplicialComplex X A).X 0 ≅ A.obj ⦋0⦌ :=
  ((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
    ComplexShape.embeddingUpNat (i := 0) rfl

/-- Pointwise tensor product of two cosimplicial objects. -/
def moduleCup_cosimplicialTensor (X : Scheme.{u})
    (A B : CosimplicialObject X.Modules) : CosimplicialObject X.Modules :=
  CategoryTheory.Monoidal.FunctorCategory.tensorObj
    (C := SimplexCategory) (D := X.Modules) A B

/-- The degree-zero pairing induced by a pointwise cosimplicial tensor morphism. -/
def moduleCup_cosimplicialZeroPair (X : Scheme.{u})
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C) :
    (moduleCup_cosimplicialComplex X A).X 0 ⊗
      (moduleCup_cosimplicialComplex X B).X 0 ⟶ (moduleCup_cosimplicialComplex X C).X 0 :=
  ((moduleCup_cosimplicialZeroIso X A).hom ⊗ₘ
    (moduleCup_cosimplicialZeroIso X B).hom) ≫ μ.app ⦋0⦌ ≫
    (moduleCup_cosimplicialZeroIso X C).inv

private theorem flasqueOfIso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N)
    (hN : TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj N)) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M) := by
  let e' := (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapIso e
  let P := ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M).obj
  let Q := ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj N).obj
  constructor
  intro U V i
  have : Epi (Q.map i) := hN.epi i
  have heq : P.map i = e'.hom.hom.app U ≫ Q.map i ≫ e'.inv.hom.app V := by
    rw [← Category.assoc, ← e'.hom.hom.naturality i, Category.assoc]
    simp
    rfl
  change Epi (P.map i)
  rw [heq]
  infer_instance

private theorem flasqueOfZero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M) := by
  constructor
  intro U V i
  have hz (W : X.Opensᵒᵖ) : IsZero (M.presheaf.obj W) := by
    let E := SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation (moduleRings X.toRingedSpace).obj W ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj W)) Ab.{u}
    exact E.map_isZero hM
  change Epi (M.presheaf.map i)
  have : IsIso (M.presheaf.map i) := (hz U).isIso (hz V) _
  infer_instance

private theorem modelFlasque {X : Scheme.{u}} {F : X.Modules}
    {A : CosimplicialObject X.Modules}
    {a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      moduleCup_cosimplicialComplex X A} (h : ModuleCupGodementModel X F A a) :
    ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
        ((moduleCup_cosimplicialComplex X A).X n)) := by
  obtain ⟨ht, _, _⟩ := h
  intro n
  by_cases hn : 0 ≤ n
  · let m := n.toNat
    have hm : (m : ℤ) = n := Int.toNat_of_nonneg hn
    let e : (moduleCup_cosimplicialComplex X A).X n ≅
        moduleCup_godementIterate X F (m + 1) :=
      (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
        ComplexShape.embeddingUpNat hm) ≪≫ eqToIso (ht m)
    exact flasqueOfIso e (moduleCup_godement_object_flasque X
      (moduleCup_godementIterate X F m))
  · have hneg : n < 0 := lt_of_not_ge hn
    have : (moduleCup_cosimplicialComplex X A).IsStrictlyGE 0 := by
      unfold moduleCup_cosimplicialComplex
      infer_instance
    exact flasqueOfZero _
      ((moduleCup_cosimplicialComplex X A).isZero_of_isStrictlyGE 0 n hneg)

/-- Flasque Godement resolutions with a pointwise cosimplicial multiplication
(Stacks, Tag 0FKR; Banerjee, §1.1.4). This supplies only a pointwise cosimplicial
multiplication, not a map of total tensor complexes. -/
theorem moduleCup_godement_cosimplicial_input (X : Scheme.{u}) (F G : X.Modules) :
    ∃ (A B C : CosimplicialObject X.Modules)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
        moduleCup_cosimplicialComplex X A)
      (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
        moduleCup_cosimplicialComplex X B)
      (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶
        moduleCup_cosimplicialComplex X C)
      (μ : moduleCup_cosimplicialTensor X A B ⟶ C),
      QuasiIso a ∧ QuasiIso b ∧ QuasiIso c ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((moduleCup_cosimplicialComplex X A).X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((moduleCup_cosimplicialComplex X B).X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((moduleCup_cosimplicialComplex X C).X n))) ∧
      ∀ (V : X.Opens)
        (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F).X 0, V))
        (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G).X 0, V)),
        (moduleCup_cosimplicialZeroPair X A B C μ).val.app (op V)
          (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y)) =
        (c.f 0).val.app (op V) (tmulSection x y) := by
  obtain ⟨A, B, C, a, b, c, μ, hA, hB, hC, hμ⟩ :=
    moduleCup_godement_model_pairing X F G
  exact ⟨A, B, C, a, b, c, μ,
    moduleCup_godement_model_quasiIso X F A a hA,
    moduleCup_godement_model_quasiIso X G B b hB,
    moduleCup_godement_model_quasiIso X (F ⊗ G) C c hC,
    modelFlasque hA, modelFlasque hB, modelFlasque hC, hμ⟩

end
end AlgebraicGeometry.Scheme.Modules
