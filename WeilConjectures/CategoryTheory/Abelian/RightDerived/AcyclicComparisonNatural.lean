/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Naturality of acyclic-resolution comparisons

Source: literature/stacks-project/derived.tex, Tag 015E.
-/

@[expose] public section

universe u v u' v'

namespace CategoryTheory

open Limits

private theorem homotopy_of_comp_quasiIso_nat
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L J : CochainComplex C ℕ} [∀ n, Injective (J.X n)]
    (α : K ⟶ L) [QuasiIso α] (β₁ β₂ : L ⟶ J)
    (w : α ≫ β₁ = α ≫ β₂) : Nonempty (Homotopy β₁ β₂) := by
  let e := ComplexShape.embeddingUpNat
  have : QuasiIso (HomologicalComplex.extendMap α e) :=
    (HomologicalComplex.quasiIso_extendMap_iff α e).2 inferInstance
  have : ∀ n, Injective ((J.extend e).X n) := fun n ↦ inferInstance
  have hw : HomologicalComplex.extendMap α e ≫ HomologicalComplex.extendMap β₁ e =
      HomologicalComplex.extendMap α e ≫ HomologicalComplex.extendMap β₂ e := by
    simp only [← HomologicalComplex.extendMap_comp, w]
  obtain ⟨ht⟩ := CochainComplex.homotopy_of_comp_quasiIso_of_injective
    (I := J.extend e)
    ⟨0, fun n hn ↦ (CochainComplex.isStrictlyGE_iff (J.extend e) 0).1
      inferInstance n hn⟩
    (HomologicalComplex.extendMap α e)
    (HomologicalComplex.extendMap β₁ e) (HomologicalComplex.extendMap β₂ e)
    ⟨Homotopy.ofEq hw⟩
  exact ⟨ht.ofExtend⟩

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C]
  [HasInjectiveResolutions C] [Abelian D]

/-- Naturality of the comparison from an acyclic resolution to a right derived functor.

Source: Stacks Project, Tag 015E, canonical acyclic-resolution comparison.
The comparison maps are the inverses of `F.rightDerivedObjIsoOfResolution`. -/
theorem acyclicComparison_naturality
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {X X' : C} {I I' : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (ι' : (CochainComplex.single₀ C).obj X' ⟶ I')
    [QuasiIso ι] [QuasiIso ι']
    (hI : ∀ n, F.rightAcyclic (I.X n))
    (hI' : ∀ n, F.rightAcyclic (I'.X n))
    (h : X ⟶ X') (φ : I ⟶ I')
    (w : ι ≫ φ = (CochainComplex.single₀ C).map h ≫ ι')
    (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n ≫
        (F.rightDerivedObjIsoOfResolution ι' hI' n).inv =
      (F.rightDerivedObjIsoOfResolution ι hI n).inv ≫ (F.rightDerived n).map h := by
  let J := injectiveResolution X
  let J' := injectiveResolution X'
  let a := InjectiveResolution.descOfQuasiIso (𝟙 X) J ι
  let a' := InjectiveResolution.descOfQuasiIso (𝟙 X') J' ι'
  let b := InjectiveResolution.desc h J' J
  have wa : ι ≫ a = J.ι := by simp [a]
  have wa' : ι' ≫ a' = J'.ι := by simp [a']
  have wb : J.ι ≫ b = (CochainComplex.single₀ C).map h ≫ J'.ι := by simp [b]
  have hw : ι ≫ (φ ≫ a') = ι ≫ (a ≫ b) := by
    rw [← Category.assoc, w, Category.assoc, wa', ← Category.assoc, wa, wb]
  obtain ⟨ht⟩ := homotopy_of_comp_quasiIso_nat ι (φ ≫ a') (a ≫ b) hw
  let H := F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n
  have heq : H.map φ ≫ H.map a' = H.map a ≫ H.map b := by
    simpa only [H, Functor.comp_map, Functor.map_comp, HomologicalComplex.homologyFunctor_map,
      HomologicalComplex.homologyMap_comp] using (F.mapHomotopy ht).homologyMap_eq n
  have hb := InjectiveResolution.isoRightDerivedObj_inv_naturality h J J' b
    (by simpa using congrArg (fun f ↦ f.f 0) wb) F n
  change H.map φ ≫ (H.map a' ≫ (J'.isoRightDerivedObj F n).inv) =
    (H.map a ≫ (J.isoRightDerivedObj F n).inv) ≫ (F.rightDerived n).map h
  rw [← Category.assoc, heq, Category.assoc, ← hb, Category.assoc]

end CategoryTheory
