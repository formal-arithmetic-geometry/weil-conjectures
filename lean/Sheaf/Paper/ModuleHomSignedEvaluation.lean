/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Signed evaluation for the ordinary module Hom complex

Source: Stacks Project, Tags 0A8H and 0A8X.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex
open scoped TensorProduct

namespace CochainComplex

variable {R : Type w} [CommRing R]
  (c V : CochainComplex (ModuleCat.{w} R) ℤ)

private def evalTerm (p j n : ℤ) (hpj : p + j = n) :
    c.X p ⊗ (moduleHomComplex c V).X j ⟶ V.X n :=
  let π : (moduleHomComplex c V).X j →ₗ[R] (c.X p →ₗ[R] V.X n) :=
    { toFun := fun h ↦ (h.v p n hpj).hom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  (p * j).negOnePow • ModuleCat.ofHom (TensorProduct.lift π.flip)

private def evalDegree (n : ℤ) :
    (HomologicalComplex.mapBifunctor c (moduleHomComplex c V)
      (curriedTensor _) (.up ℤ)).X n ⟶ V.X n :=
  HomologicalComplex.mapBifunctorDesc (fun p j hpj ↦ evalTerm c V p j n hpj)

private theorem evalDegree_ι (p j n : ℤ) (hpj : p + j = n) :
    HomologicalComplex.ιMapBifunctor c (moduleHomComplex c V) (curriedTensor _) (.up ℤ) p j n hpj ≫
      evalDegree c V n = evalTerm c V p j n hpj :=
  HomologicalComplex.ι_mapBifunctorDesc _ p j hpj

private theorem evalTerm_apply (p j n : ℤ) (hpj : p + j = n)
    (x : c.X p) (h : (moduleHomComplex c V).X j) :
    (evalTerm c V p j n hpj).hom (x ⊗ₜ[R] h) =
      (p * j).negOnePow • (h.v p n hpj).hom x := by
  rfl

private theorem evalDegree_comm (n m : ℤ) (hnm : n + 1 = m) :
    evalDegree c V n ≫ V.d n m =
      (HomologicalComplex.mapBifunctor c (moduleHomComplex c V) (curriedTensor _) (.up ℤ)).d n m ≫
        evalDegree c V m := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p j hpj
  change p + j = n at hpj
  subst n
  rw [← Category.assoc, evalDegree_ι]
  have hd : HomologicalComplex.ιMapBifunctor c (moduleHomComplex c V)
      (curriedTensor _) (.up ℤ) p j (p + j) rfl ≫
        (HomologicalComplex.mapBifunctor c (moduleHomComplex c V)
          (curriedTensor _) (.up ℤ)).d (p + j) m =
      c.d p (p + 1) ▷ (moduleHomComplex c V).X j ≫
        HomologicalComplex.ιMapBifunctor c (moduleHomComplex c V)
          (curriedTensor _) (.up ℤ) (p + 1) j m (show p + 1 + j = m by omega) +
      p.negOnePow • (c.X p ◁ (moduleHomComplex c V).d j (j + 1) ≫
        HomologicalComplex.ιMapBifunctor c (moduleHomComplex c V)
          (curriedTensor _) (.up ℤ) p (j + 1) m (show p + (j + 1) = m by omega)) := by
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _ (by dsimp; omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
        (rfl : (ComplexShape.up ℤ).Rel j (j + 1)) _ (by dsimp; omega)]
    simp
  rw [← Category.assoc, hd, Preadditive.add_comp]
  simp only [Units.smul_def, Preadditive.zsmul_comp, Category.assoc,
    evalDegree_ι]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
    LinearMap.add_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  change (V.d (p + j) m).hom ((p * j).negOnePow • (h.v p (p + j) rfl).hom x) =
    (evalTerm c V (p + 1) j m (by omega)).hom ((c.d p (p + 1)).hom x ⊗ₜ[R] h) +
      (p.negOnePow : ℤ) •
        (evalTerm c V p (j + 1) m (by omega)).hom
          (x ⊗ₜ[R] δ j (j + 1) h)
  rw [evalTerm_apply, evalTerm_apply]
  rw [δ_v j (j + 1) rfl h p m (by omega) (p + j) (p + 1) (by omega) rfl]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
  have hs₀ : p.negOnePow * (p * (j + 1)).negOnePow = (p * j).negOnePow := by
    rw [← Int.negOnePow_add, show p + p * (j + 1) = p * j + 2 * p by ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  have hs : (p.negOnePow : ℤ) * ((p * (j + 1)).negOnePow : ℤ) =
      ((p * j).negOnePow : ℤ) := congrArg Units.val hs₀
  have hb : (((p + 1) * j).negOnePow : ℤ) =
      ((p * j).negOnePow : ℤ) * (j.negOnePow : ℤ) := by
    rw [show (p + 1) * j = p * j + j by ring, Int.negOnePow_add]
    rfl
  simp only [Units.smul_def, map_zsmul, smul_smul, hs, hb,
    Int.negOnePow_succ, Units.val_neg, smul_add, neg_smul]
  simp only [smul_neg, smul_smul]
  abel

/-- Ordinary evaluation with the argument before Hom has the Koszul sign.
Source: Stacks Project, Tags 0A8H and 0A8X
(blueprint: lem-pod-module-hom-signed-evaluation).

Proof: in bidegree (p,j), apply the p-th Hom component to x and multiply
by (-1)^(pj). Extend this bilinear map through the tensor and coproduct universal
properties. The Hom differential and total tensor differential show the two
terms containing h(dx) cancel. The remaining term is d(h(x)), with the original
sign. Thus the maps in each total degree give a chain map, including for
unbounded complexes. The coproduct insertion equation gives the formula. -/
theorem module_hom_signed_evaluation :
    ∃ e : HomologicalComplex.mapBifunctor c (moduleHomComplex c V) (curriedTensor _) (.up ℤ) ⟶ V,
      ∀ (p j : ℤ) (x : c.X p) (h : (moduleHomComplex c V).X j),
        (e.f (p + j)).hom
          ((HomologicalComplex.ιMapBifunctor c (moduleHomComplex c V) (curriedTensor _) (.up ℤ)
            p j (p + j) rfl).hom (x ⊗ₜ[R] h)) =
          (p * j).negOnePow • (h.v p (p + j) rfl).hom x := by
  let e : HomologicalComplex.mapBifunctor c (moduleHomComplex c V) (curriedTensor _) (.up ℤ) ⟶ V :=
    { f := evalDegree c V
      comm' := evalDegree_comm c V }
  refine ⟨e, ?_⟩
  intro p j x h
  exact congrArg (fun f ↦ f.hom (x ⊗ₜ[R] h)) (evalDegree_ι c V p j (p + j) rfl)

end CochainComplex
