/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Sheaf.Paper.CoefficientDuality
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Sheaf.Algebra.Homology.PerfectDualDerivedTransport
import Mathlib.LinearAlgebra.Contraction
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.RingTheory.Localization.BaseChange
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.RingTheory.OreLocalization.Ring
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all Mathlib.Algebra.Category.ModuleCat.Localization
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Signed perfect-dual scalar calculus

Source: Stacks Project, Tags 00CV, 05G3, 07VI, 0A8H, 0FNG, 064B and 00CS;
blueprint, point dualizing complex, coefficient-ring computation of derived Hom
(blueprint: lem-pod-perfect-dual-scalar-calculus).

Scalar extension uses the recorded scalar-first tensor model `S ⊗[R] P`.
The ordinary dual uses the recorded product Hom complex, not a second Hom construction.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open DerivedCategory DerivedCategory.PerfectScalar WeilConjectures Opposite
open scoped TensorProduct ChangeOfRings

namespace CochainComplex.PerfectDualScalar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


private noncomputable def preMap {R : CommRingCat.{u}}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (v : P ⟶ Q) :
    moduleHomComplex Q (coefficient R) ⟶ moduleHomComplex P (coefficient R) where
  f n := ModuleCat.ofHom
    { toFun := fun z ↦ (HomComplex.Cochain.ofHom v).comp z (zero_add n)
      map_add' := fun z w ↦ by simp
      map_smul' := fun r z ↦ by simp }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact HomComplex.δ_ofHom_comp v z m

private lemma preMap_v {R : CommRingCat.{u}}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (v : P ⟶ Q)
    (n p q : ℤ) (h : p + n = q) (z : (moduleHomComplex Q (coefficient R)).X n) :
    ((preMap v).f n z).v p q h = v.f p ≫ z.v p q h := by
  exact HomComplex.Cochain.zero_cochain_comp_v _ _ _ _ _

private lemma extend_smul {R S : CommRingCat.{u}} (f : R ⟶ S)
    {M N : ModuleCat.{u} R} (r : R) (z : M ⟶ N) :
    (ModuleCat.extendScalars f.hom).map (r • z) =
      f.hom r • (ModuleCat.extendScalars f.hom).map z := by
  let := f.hom.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (1 : S) ⊗ₜ[R] (r • z x) = f.hom r • ((1 : S) ⊗ₜ[R] z x)
  rw [TensorProduct.tmul_smul]
  rfl

private noncomputable def scalarCochain {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (moduleHomComplex P (coefficient R)).X n ⟶
      (ModuleCat.restrictScalars f.hom).obj
        ((moduleHomComplex ((E f).obj P) (coefficient S)).X n) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars f.hom).obj
    ((moduleHomComplex ((E f).obj P) (coefficient S)).X n))
    { toFun := fun z ↦ (z.map (ModuleCat.extendScalars f.hom)).comp
        (HomComplex.Cochain.ofHom
          (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv) (add_zero n)
      map_add' := fun z w ↦ by simp
      map_smul' := fun r z ↦ by
        change ((r • z).map (ModuleCat.extendScalars f.hom)).comp
          (HomComplex.Cochain.ofHom
            (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv) (add_zero n) =
          f.hom r • ((z.map (ModuleCat.extendScalars f.hom)).comp
            (HomComplex.Cochain.ofHom
              (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv) (add_zero n))
        apply HomComplex.Cochain.ext
        intro p q h
        simp only [HomComplex.Cochain.smul_v, HomComplex.Cochain.comp_zero_cochain_v,
          HomComplex.Cochain.map_v, HomComplex.Cochain.ofHom_v]
        rw [extend_smul, Linear.smul_comp] }

attribute [irreducible] scalarCochain

private lemma scalarCochain_apply {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (z : (moduleHomComplex P (coefficient R)).X n) :
    scalarCochain f P n z = (z.map (ModuleCat.extendScalars f.hom)).comp
      (HomComplex.Cochain.ofHom
        (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv) (add_zero n) := by
  unfold scalarCochain
  rfl

private noncomputable def betaX {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (ModuleCat.extendScalars f.hom).obj ((moduleHomComplex P (coefficient R)).X n) ⟶
      (moduleHomComplex ((E f).obj P) (coefficient S)).X n :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f.hom
    (scalarCochain f P n)

attribute [irreducible] betaX

private lemma betaX_one {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (z : (moduleHomComplex P (coefficient R)).X n) :
    let := f.hom.toAlgebra
    betaX f P n ((1 : S) ⊗ₜ[R] z) = scalarCochain f P n z := by
  unfold betaX
  change (1 : S) • scalarCochain f P n z = _
  exact one_smul _ _

private noncomputable def betaMap {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (E f).obj (moduleHomComplex P (coefficient R)) ⟶
      moduleHomComplex ((E f).obj P) (coefficient S) where
  f n := betaX f P n
  comm' n m _ := by
    let := f.hom.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro z
    change HomComplex.δ n m (betaX f P n ((1 : S) ⊗ₜ[R] z)) =
      betaX f P m ((1 : S) ⊗ₜ[R] HomComplex.δ n m z)
    rw [betaX_one, betaX_one, scalarCochain_apply, scalarCochain_apply,
      HomComplex.δ_comp_ofHom, HomComplex.δ_map]

private lemma betaX_tmul {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (a : S) (z : (moduleHomComplex P (coefficient R)).X n) :
    letI := f.hom.toAlgebra
    betaX f P n (a ⊗ₜ[R] z) = a • scalarCochain f P n z := by
  let := f.hom.toAlgebra
  rw [show a ⊗ₜ[R] z = a • ((1 : S) ⊗ₜ[R] z) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  exact ((betaX f P n).hom.map_smul a _).trans (congrArg (a • ·) (betaX_one f P n z))

private lemma coefficient_unit_apply {R S : CommRingCat.{u}} (f : R ⟶ S)
    (a : S) (r : (coefficient R).X 0) :
    letI := f.hom.toAlgebra
    (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv.f 0 (a ⊗ₜ[R] r) =
      f.hom r * a := by
  rfl

private lemma betaMap_apply {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (p j : ℤ) (h : p + j = 0)
    (z : (moduleHomComplex P (coefficient R)).X j) (x : P.X p) (a b : S) :
    letI := f.hom.toAlgebra
    (((betaMap f P).f j (a ⊗ₜ[R] z)).v p 0 h) (b ⊗ₜ[R] x) =
      f.hom ((z.v p 0 h) x) * a * b := by
  let := f.hom.toAlgebra
  change ((betaX f P j (a ⊗ₜ[R] z)).v p 0 h) (b ⊗ₜ[R] x) = _
  rw [betaX_tmul, HomComplex.Cochain.smul_v, scalarCochain_apply,
    HomComplex.Cochain.comp_zero_cochain_v, HomComplex.Cochain.map_v,
    HomComplex.Cochain.ofHom_v]
  change a • ((ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv.f 0
    ((ModuleCat.extendScalars f.hom).map (z.v p 0 h) (b ⊗ₜ[R] x))) = _
  rw [ModuleCat.ExtendScalars.map_tmul, coefficient_unit_apply]
  change a * (f.hom ((z.v p 0 h) x) * b) = _
  ac_rfl

private noncomputable def dualXEquiv (R : CommRingCat.{u})
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (moduleHomComplex P (coefficient R)).X n ≃ₗ[R] Module.Dual R (P.X (-n)) :=
  { (HomComplex.Cochain.toSingleEquiv (K := P)
      (X := ModuleCat.of R R) (show -n + n = 0 by omega)).trans
      (ModuleCat.homLinearEquiv (S := R)).toAddEquiv with
    map_smul' := fun r z ↦ by
      apply LinearMap.ext
      intro x
      change ((r • z).v (-n) 0 (by omega) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).hom) x = _
      rw [HomComplex.Cochain.smul_v, Linear.smul_comp]
      rfl }

private lemma dualX_finite_projective (R : CommRingCat.{u})
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (ht : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)) (n : ℤ) :
    Module.Projective R ((moduleHomComplex P (coefficient R)).X n) ∧
      Module.Finite R ((moduleHomComplex P (coefficient R)).X n) := by
  have := (ht (-n)).1
  have := (ht (-n)).2
  exact ⟨Module.Projective.of_equiv (dualXEquiv R P n).symm,
    Module.Finite.equiv (dualXEquiv R P n).symm⟩

private lemma scalar_terms {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (ht : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)) (n : ℤ) :
    Module.Projective S (((E f).obj P).X n) ∧
      Module.Finite S (((E f).obj P).X n) := by
  let := f.hom.toAlgebra
  have := (ht n).1
  have := (ht n).2
  change Module.Projective S (S ⊗[R] P.X n) ∧ Module.Finite S (S ⊗[R] P.X n)
  exact ⟨inferInstance, inferInstance⟩

private noncomputable def ordinaryDualEquiv {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : ModuleCat.{u} R) [Module.Projective R M] [Module.Finite R M] :
    letI := f.hom.toAlgebra
    (S ⊗[R] Module.Dual R M) ≃+
      Module.Dual S ((ModuleCat.extendScalars f.hom).obj M) := by
  let := f.hom.toAlgebra
  exact (TensorProduct.comm R S (Module.Dual R M)).toAddEquiv.trans
    ((dualTensorHomEquiv R M
      ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of S S))).toAddEquiv.trans
      (ModuleCat.homAddEquiv.symm.trans
        (((ModuleCat.extendRestrictScalarsAdj f.hom).homAddEquiv M
          (ModuleCat.of S S)).symm.trans ModuleCat.homAddEquiv)))

private lemma ordinaryDualEquiv_apply {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : ModuleCat.{u} R) [Module.Projective R M] [Module.Finite R M]
    (a b : S) (z : Module.Dual R M) (x : M) :
    letI := f.hom.toAlgebra
    ordinaryDualEquiv f M (a ⊗ₜ[R] z) (b ⊗ₜ[R] x) = f.hom (z x) * a * b := by
  let := f.hom.toAlgebra
  change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f.hom
    (X := M) (Y := ModuleCat.of S S)
    (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of S S))
      (dualTensorHom R M
      ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of S S)) (z ⊗ₜ[R] a))))
        (b ⊗ₜ[R] x) = _
  change b * (f.hom (z x) * a) = _
  ac_rfl

private lemma betaX_isIso {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (ht : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)) (n : ℤ) :
    IsIso (betaX f P n) := by
  let := f.hom.toAlgebra
  have := (ht (-n)).1
  have := (ht (-n)).2
  let e : ((ModuleCat.extendScalars f.hom).obj
      ((moduleHomComplex P (coefficient R)).X n)) ≃+
        Module.Dual S (((E f).obj P).X (-n)) :=
    (LinearEquiv.baseChange R S _ _ (dualXEquiv R P n)).toAddEquiv.trans
      (ordinaryDualEquiv f (P.X (-n)))
  have he : ∀ z, dualXEquiv S ((E f).obj P) n (betaX f P n z) = e z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a z =>
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        change (((betaX f P n (a ⊗ₜ[R] z)).v (-n) 0 (by omega)) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of S S)).hom)
            (b ⊗ₜ[R] x) = _
        change ((betaMap f P).f n (a ⊗ₜ[R] z)).v (-n) 0 (by omega) (b ⊗ₜ[R] x) = _
        rw [betaMap_apply]
        change _ = ordinaryDualEquiv f (P.X (-n))
          (a ⊗ₜ[R] dualXEquiv R P n z) (b ⊗ₜ[R] x)
        rw [ordinaryDualEquiv_apply]
        rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have hh : Function.Bijective ((dualXEquiv S ((E f).obj P) n) ∘ betaX f P n) := by
    convert e.bijective using 1
    exact funext he
  exact (Function.Bijective.of_comp_iff'
    (dualXEquiv S ((E f).obj P) n).bijective (betaX f P n)).1 hh

private lemma beta_isIso {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (ht : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)) :
    IsIso (betaMap f P) := by
  have : ∀ n : ℤ, IsIso ((betaMap f P).f n) := betaX_isIso f P ht
  exact HomologicalComplex.Hom.isIso_of_components _

private lemma beta_naturality {R S : CommRingCat.{u}} (f : R ⟶ S)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (v : P ⟶ Q) :
    (E f).map (preMap v) ≫ betaMap f P =
      betaMap f Q ≫ preMap ((E f).map v) := by
  let := f.hom.toAlgebra
  ext n : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  apply (dualXEquiv S ((E f).obj P) n).injective
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    change (((betaMap f P).f n
      ((ModuleCat.extendScalars f.hom).map ((preMap v).f n) ((1 : S) ⊗ₜ[R] z))).v
        (-n) 0 (by omega)) (b ⊗ₜ[R] x) =
      (((preMap ((E f).map v)).f n ((betaMap f Q).f n ((1 : S) ⊗ₜ[R] z))).v
        (-n) 0 (by omega)) (b ⊗ₜ[R] x)
    rw [ModuleCat.ExtendScalars.map_tmul, betaMap_apply]
    rw [preMap_v, preMap_v]
    change _ = ((betaMap f Q).f n ((1 : S) ⊗ₜ[R] z)).v (-n) 0 (by omega)
      (b ⊗ₜ[R] v.f (-n) x)
    rw [betaMap_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma beta_tower_apply {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (p j : ℤ) (h : p + j = 0)
    (z : (moduleHomComplex P (coefficient R)).X j) (x : P.X p) (a b : S) (c d : T) :
    letI := f.hom.toAlgebra
    letI := g.hom.toAlgebra
    (((betaMap g ((E f).obj P)).f j
      (c ⊗ₜ[S] ((betaMap f P).f j (a ⊗ₜ[R] z)))).v p 0 h)
        (d ⊗ₜ[S] (b ⊗ₜ[R] x)) =
      g.hom (f.hom ((z.v p 0 h) x)) * g.hom (a * b) * c * d := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  rw [betaMap_apply, betaMap_apply, map_mul, map_mul, map_mul]
  ac_rfl

private lemma beta_evaluation
    (ev : ∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ),
      P ⊗ moduleHomComplex P (coefficient R) ⟶ coefficient R)
    (hev : ∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (p j : ℤ) (x : P.X p) (z : (moduleHomComplex P (coefficient R)).X j),
      (ev R P).f (p + j)
        (HomologicalComplex.ιTensorObj P (moduleHomComplex P (coefficient R)) p j (p + j) rfl
          (x ⊗ₜ[R] z)) = (p * j).negOnePow • (z.v p (p + j) rfl) x)
    {R S : CommRingCat.{u}} (f : R ⟶ S) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars f.hom).mapCochainComplexμIso P
        (moduleHomComplex P (coefficient R))).hom ≫
      (E f).map (ev R P) ≫ (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv =
        (E f).obj P ◁ betaMap f P ≫ ev S ((E f).obj P) := by
  let := f.hom.toAlgebra
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p j h
  subst n
  by_cases hn : p + j = 0
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x z
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a z =>
        change S at a b
        simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
          ← Category.assoc]
        rw [Functor.ιTensorObj_mapCochainComplexμIso_hom_f]
        simp only [Category.assoc]
        rw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc]
        rw [ModuleCat.extendScalars_μ]
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        change (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv.f (p + j)
          ((ModuleCat.extendScalars f.hom).map ((ev R P).f (p + j))
            ((ModuleCat.extendScalars f.hom).map
              (HomologicalComplex.ιTensorObj P (moduleHomComplex P (coefficient R))
                p j (p + j) rfl)
                ((TensorProduct.AlgebraTensorModule.distribBaseChange R S
                  (P.X p) ((moduleHomComplex P (coefficient R)).X j)).symm
                    ((b ⊗ₜ[R] x) ⊗ₜ[S] (a ⊗ₜ[R] z))))) =
          (ev S ((E f).obj P)).f (p + j)
            (HomologicalComplex.ιTensorObj ((E f).obj P)
              (moduleHomComplex ((E f).obj P) (coefficient S)) p j (p + j) rfl
                ((b ⊗ₜ[R] x) ⊗ₜ[S] (betaMap f P).f j (a ⊗ₜ[R] z)))
        rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
          ModuleCat.ExtendScalars.map_tmul, ModuleCat.ExtendScalars.map_tmul, hev, hev]
        have hcalc (q : ℤ) (hq : p + j = q) (hq0 : q = 0) :
            (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv.f q
              ((b * a) ⊗ₜ[R] ((p * j).negOnePow • (z.v p q hq) x)) =
                (p * j).negOnePow •
                  (((betaMap f P).f j (a ⊗ₜ[R] z)).v p q hq) (b ⊗ₜ[R] x) := by
          cases hq0
          rw [coefficient_unit_apply, betaMap_apply]
          rcases Int.units_eq_one_or (p * j).negOnePow with hs | hs <;>
            simp [hs, map_neg] <;> ac_rfl
        exact hcalc (p + j) rfl hn
      | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (ModuleCat.of S S) (p + j) hn).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def localizationModuleIso (R : CommRingCat.{u}) (U : Submonoid R) :
    ModuleCat.extendScalars (algebraMap R (Localization U)) ≅
      ModuleCat.localizedModuleFunctor U :=
  NatIso.ofComponents (fun M ↦ by
    let L := Localization U
    let e := (IsLocalizedModule.isBaseChange U L
      (M.localizedModuleMkLinearMap U)).equiv
    let e₀ : ((ModuleCat.restrictScalars (algebraMap R L)).obj
        (ModuleCat.of L L)) ≃ₗ[L] L :=
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    letI : IsScalarTower R L ((ModuleCat.restrictScalars (algebraMap R L)).obj
        (ModuleCat.of L L)) := ⟨fun r s t ↦ by
      change L at t
      change (r • s : L) * t = algebraMap R L r * (s * t)
      rw [Algebra.smul_def]
      exact mul_assoc _ _ _⟩
    let e₁ := TensorProduct.AlgebraTensorModule.congr e₀ (LinearEquiv.refl R M)
    exact e₁.toModuleIso ≪≫ e.toModuleIso) (by
    intro M N v
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (IsLocalizedModule.isBaseChange U (Localization U)
        (N.localizedModuleMkLinearMap U)).equiv ((1 : Localization U) ⊗ₜ[R] v x) =
      IsLocalizedModule.mapExtendScalars U (M.localizedModuleMkLinearMap U)
        (N.localizedModuleMkLinearMap U) (Localization U) v.hom
        ((IsLocalizedModule.isBaseChange U (Localization U)
          (M.localizedModuleMkLinearMap U)).equiv ((1 : Localization U) ⊗ₜ[R] x))
    simp [IsBaseChange.equiv_tmul])

attribute [irreducible] localizationModuleIso

private lemma localizationModuleIso_one (R : CommRingCat.{u}) (U : Submonoid R)
    (M : ModuleCat.{u} R) (x : M) :
    (localizationModuleIso R U).hom.app M ((1 : Localization U) ⊗ₜ[R] x) =
      M.localizedModuleMkLinearMap U x := by
  unfold localizationModuleIso
  change (IsLocalizedModule.isBaseChange U (Localization U)
    (M.localizedModuleMkLinearMap U)).equiv ((1 : Localization U) ⊗ₜ[R] x) = _
  rw [IsBaseChange.equiv_tmul, one_smul]

set_option backward.isDefEq.respectTransparency false in
private lemma localizationModuleIso_inv_mk (R : CommRingCat.{u}) (U : Submonoid R)
    (M : ModuleCat.{u} R) (x : M) (s : U) :
    (localizationModuleIso R U).inv.app M
      (@id (M.localizedModule U)
        (IsLocalizedModule.mk' (M.localizedModuleMkLinearMap U) x s)) =
        IsLocalization.mk' (Localization U) 1 s ⊗ₜ[R,algebraMap R (Localization U)] x := by
  apply (ConcreteCategory.bijective_of_isIso ((localizationModuleIso R U).hom.app M)).1
  change ((localizationModuleIso R U).inv.app M ≫
    (localizationModuleIso R U).hom.app M)
      (@id (M.localizedModule U)
        (IsLocalizedModule.mk' (M.localizedModuleMkLinearMap U) x s)) = _
  rw [Iso.inv_hom_id_app]
  change IsLocalizedModule.mk' (M.localizedModuleMkLinearMap U) x s = _
  rw [show IsLocalization.mk' (Localization U) 1 s ⊗ₜ[R,algebraMap R (Localization U)] x =
      IsLocalization.mk' (Localization U) 1 s •
        ((1 : Localization U) ⊗ₜ[R,algebraMap R (Localization U)] x) by
        rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]]
  rw [map_smul, localizationModuleIso_one]
  simpa only [one_smul, mul_one, IsLocalizedModule.mk'_one] using
    (IsLocalizedModule.mk'_smul_mk' (f := M.localizedModuleMkLinearMap U)
      (Localization U) 1 x s 1).symm

private lemma beta_identity (R : CommRingCat.{u})
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    betaMap (𝟙 R) P ≫
      preMap ((NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsId R) (.up ℤ)).app P).inv =
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) (.up ℤ)).app
        (moduleHomComplex P (coefficient R))).hom := by
  ext n : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  apply (dualXEquiv R P n).injective
  apply LinearMap.ext
  intro x
  change (((preMap ((NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsId R) (.up ℤ)).app P).inv).f n
      ((betaMap (𝟙 R) P).f n ((1 : R) ⊗ₜ[R] z))).v (-n) 0 (by omega)) x = _
  rw [preMap_v]
  change ((betaMap (𝟙 R) P).f n ((1 : R) ⊗ₜ[R] z)).v (-n) 0 (by omega)
    ((1 : R) ⊗ₜ[R] x) = _
  rw [betaMap_apply]
  change _ = ((ModuleCat.extendScalarsId R).hom.app
    ((moduleHomComplex P (coefficient R)).X n) ((1 : R) ⊗ₜ[R] z)).v
      (-n) 0 (by omega) x
  rw [ModuleCat.extendScalarsId_hom_app_one_tmul]
  simp

private lemma scalar_hom_ext₂ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} T)
    (v w : (ModuleCat.extendScalars g.hom).obj
      ((ModuleCat.extendScalars f.hom).obj M) ⟶ N)
    (h : ∀ x : M, v ((1 : T) ⊗ₜ[S,g.hom] ((1 : S) ⊗ₜ[R,f.hom] x)) =
      w ((1 : T) ⊗ₜ[S,g.hom] ((1 : S) ⊗ₜ[R,f.hom] x))) : v = w := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    change S at b
    have he : (1 : T) ⊗ₜ[S,g.hom] (b ⊗ₜ[R,f.hom] x) =
        g.hom b • ((1 : T) ⊗ₜ[S,g.hom] ((1 : S) ⊗ₜ[R,f.hom] x)) := by
      let := f.hom.toAlgebra
      let := g.hom.toAlgebra
      rw [show b ⊗ₜ[R,f.hom] x = b • ((1 : S) ⊗ₜ[R,f.hom] x) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      rw [TensorProduct.tmul_smul]
      rfl
    rw [he, map_smul, map_smul, h]
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]

private lemma scalar_comp_inv_one {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (M : ModuleCat.{u} R) (x : M) :
    (ModuleCat.extendScalarsComp f.hom g.hom).inv.app M
      ((1 : T) ⊗ₜ[S,g.hom] ((1 : S) ⊗ₜ[R,f.hom] x)) =
        (1 : T) ⊗ₜ[R,(g.hom.comp f.hom)] x := by
  rw [← ModuleCat.extendScalarsComp_hom_app_one_tmul f.hom g.hom M x]
  change ((ModuleCat.extendScalarsComp f.hom g.hom).hom.app M ≫
    (ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

private lemma beta_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (E g).map (betaMap f P) ≫ betaMap g ((E f).obj P) =
      ((NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsComp f.hom g.hom).symm (.up ℤ)).app
          (moduleHomComplex P (coefficient R))).hom ≫ betaMap (f ≫ g) P ≫
        preMap ((NatIso.mapHomologicalComplex
          (ModuleCat.extendScalarsComp f.hom g.hom).symm (.up ℤ)).app P).hom := by
  ext n : 1
  apply scalar_hom_ext₂ f g
  intro z
  apply (dualXEquiv T ((E g).obj ((E f).obj P)) n).injective
  apply ModuleCat.homEquiv.symm.injective
  apply scalar_hom_ext₂ f g
  intro x
  change (((betaMap g ((E f).obj P)).f n
    ((ModuleCat.extendScalars g.hom).map ((betaMap f P).f n)
      ((1 : T) ⊗ₜ[S,g.hom] ((1 : S) ⊗ₜ[R,f.hom] z)))).v (-n) 0 (by omega))
        ((1 : T) ⊗ₜ[S,g.hom] ((1 : S) ⊗ₜ[R,f.hom] x)) = _
  rw [ModuleCat.ExtendScalars.map_tmul, betaMap_apply, betaMap_apply]
  change _ = ((preMap ((NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp f.hom g.hom).symm (.up ℤ)).app P).hom).f n
      ((betaMap (f ≫ g) P).f n
        ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app
          ((moduleHomComplex P (coefficient R)).X n)
            ((1 : T) ⊗ₜ[S,g.hom] ((1 : S) ⊗ₜ[R,f.hom] z))))).v
              (-n) 0 (by omega) ((1 : T) ⊗ₜ[S,g.hom] ((1 : S) ⊗ₜ[R,f.hom] x))
  rw [scalar_comp_inv_one, preMap_v]
  change _ = ((betaMap (f ≫ g) P).f n ((1 : T) ⊗ₜ[R,(g.hom.comp f.hom)] z)).v
    (-n) 0 (by omega) ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app (P.X (-n))
      ((1 : T) ⊗ₜ[S,g.hom] ((1 : S) ⊗ₜ[R,f.hom] x)))
  rw [scalar_comp_inv_one, betaMap_apply]
  simp

private lemma dual_perfect [∀ R : CommRingCat.{u},
    HasDerivedCategory.{u} (ModuleCat.{u} R)] (R : CommRingCat.{u}) (P : D R)
    (hP : IsPerfectRingComplex P) :
    IsPerfectRingComplex ((coefficientDerivedDual R).obj (op P)) :=
  DerivedCategory.IsPerfect.ihom_unit hP

private lemma localization_quasiIso (R : CommRingCat.{u}) (U : Submonoid R)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (v : P ⟶ Q) (hv : QuasiIso v) :
    QuasiIso (((ModuleCat.localizedModuleFunctor U).mapHomologicalComplex (.up ℤ)).map v) := by
  have := hv
  infer_instance

/-- Signed scalar calculus, with one simultaneous family for every coefficient map.
Source: Stacks 00CV, 05G3, 07VI, 0A8H, 0FNG, 064B, 00CS and blueprint point duality
(blueprint: lem-pod-perfect-dual-scalar-calculus).

Proof: Identify each degree of Hom into the coefficient complex with the ordinary
module dual by the Hom-to-single equivalence. Construct beta by scalar extension
of cochain components and the coefficient-unit map. The Hom differential composition
identities make it a chain map. Mathlib's dualTensorHomEquiv and the scalar adjunction
supply its degreewise inverse for finite-projective terms, with no flatness assumption.
The signed evaluation model supplies evaluation; direct calculations on pure tensors
prove its scalar square and beta naturality, identity and tower equations. Apply
perfect_dual_derived_transport, whose canonical curried evaluation comparison preserves
perfect dual pairings, for all five derived clauses. Exactness of module localization
preserves quasi-isomorphisms. Its base-change universal property identifies scalar
extension with localization, and the beta coordinate formula gives z(x)/(s*t) for
localized fractions, including zero localizations. -/
theorem perfect_dual_scalar_calculus
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u} (ModuleCat.{u} R)] :
    ∃ pre : ∀ (R : CommRingCat.{u}) {P Q : CochainComplex (ModuleCat.{u} R) ℤ},
        (P ⟶ Q) → ((moduleHomComplex Q (coefficient R)) ⟶ (moduleHomComplex P (coefficient R))),
    ∃ ev : ∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ),
        P ⊗ (moduleHomComplex P (coefficient R)) ⟶ coefficient R,
    ∃ beta : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
        (P : CochainComplex (ModuleCat.{u} R) ℤ),
        (E f).obj (moduleHomComplex P (coefficient R)) ⟶ (moduleHomComplex ((E f).obj P)
          (coefficient S)),
    ∃ dualPerfect : ∀ (R : CommRingCat.{u}) (P : D.{u, u} R),
        IsPerfectRingComplex P → IsPerfectRingComplex ((coefficientDerivedDual R).obj (op P)),
    ∃ delta : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P : D.{u, u} R),
        IsPerfectRingComplex P →
          ((B f).obj ((coefficientDerivedDual R).obj (op P)) ≅ ((coefficientDerivedDual S).obj
            (op ((B f).obj P)))),
      (∀ (R : CommRingCat.{u}) (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
          (v : P ⟶ Q) (p j : ℤ) (h : p + j = 0) (z : (moduleHomComplex Q (coefficient R)).X j),
        ((pre R v).f j z).v p 0 h = v.f p ≫ z.v p 0 h) ∧
      (∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ)
          (p j : ℤ) (x : P.X p) (z : (moduleHomComplex P (coefficient R)).X j),
        (ev R P).f (p + j)
          (HomologicalComplex.ιTensorObj P (moduleHomComplex P (coefficient R)) p j (p + j) rfl
            (x ⊗ₜ[R] z)) =
            (p * j).negOnePow • (z.v p (p + j) rfl) x) ∧
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
          (P : CochainComplex (ModuleCat.{u} R) ℤ) (p j : ℤ) (h : p + j = 0)
          (z : (moduleHomComplex P (coefficient R)).X j) (x : P.X p) (a b : S),
        (((beta f P).f j (a ⊗ₜ[R] z)).v p 0 h) (b ⊗ₜ[R] x) =
          f.hom ((z.v p 0 h) x) * a * b) ∧
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
          (P : CochainComplex (ModuleCat.{u} R) ℤ),
        ((ModuleCat.extendScalars f.hom).mapCochainComplexμIso P (moduleHomComplex P (coefficient
          R))).hom ≫
            (E f).map (ev R P) ≫
            (ModuleCat.extendScalars f.hom).mapCochainComplexεIso.inv =
          (E f).obj P ◁ beta f P ≫ ev S ((E f).obj P)) ∧
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
          (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
          (_hlo : P.IsStrictlyGE a) (_hhi : P.IsStrictlyLE b)
          (_ht : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)),
        IsIso (beta f P) ∧
        (∀ n : ℤ, Module.Projective S (((E f).obj P).X n) ∧
          Module.Finite S (((E f).obj P).X n)) ∧
        (∀ n : ℤ, Module.Projective R ((moduleHomComplex P (coefficient R)).X n) ∧
          Module.Finite R ((moduleHomComplex P (coefficient R)).X n)) ∧
        (∀ n : ℤ, Module.Projective S ((moduleHomComplex ((E f).obj P) (coefficient S)).X n) ∧
          Module.Finite S ((moduleHomComplex ((E f).obj P) (coefficient S)).X n))) ∧
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
          (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (v : P ⟶ Q),
        (E f).map (pre R v) ≫ beta f P =
          beta f Q ≫ pre S ((E f).map v)) ∧
      (∀ (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ),
        beta (𝟙 R) P ≫
            pre R ((NatIso.mapHomologicalComplex
              (ModuleCat.extendScalarsId R) (.up ℤ)).app P).inv =
          ((NatIso.mapHomologicalComplex
            (ModuleCat.extendScalarsId R) (.up ℤ)).app (moduleHomComplex P (coefficient
              R))).hom) ∧
      (∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
          (P : CochainComplex (ModuleCat.{u} R) ℤ),
        (E g).map (beta f P) ≫ beta g ((E f).obj P) =
          ((NatIso.mapHomologicalComplex
            (ModuleCat.extendScalarsComp f.hom g.hom).symm (.up ℤ)).app (moduleHomComplex P
              (coefficient R))).hom ≫
          beta (f ≫ g) P ≫ pre T ((NatIso.mapHomologicalComplex
            (ModuleCat.extendScalarsComp f.hom g.hom).symm (.up ℤ)).app P).hom) ∧
      (∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
          (P : CochainComplex (ModuleCat.{u} R) ℤ) (p j : ℤ) (h : p + j = 0)
          (z : (moduleHomComplex P (coefficient R)).X j) (x : P.X p) (a b : S) (c d : T),
        (((beta g ((E f).obj P)).f j
            (c ⊗ₜ[S] ((beta f P).f j (a ⊗ₜ[R] z)))).v p 0 h)
            (d ⊗ₜ[S] (b ⊗ₜ[R] x)) =
          g.hom (f.hom ((z.v p 0 h) x)) * g.hom (a * b) * c * d) ∧
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (P Q : D.{u, u} R)
          (hP : IsPerfectRingComplex P) (hQ : IsPerfectRingComplex Q) (v : P ⟶ Q),
        (B f).map ((MonoidalClosed.pre v).app (𝟙_ (D R))) ≫ (delta f P hP).hom =
          (delta f Q hQ).hom ≫
            (MonoidalClosed.pre ((B f).map v)).app (𝟙_ (D S))) ∧
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
          (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
          (_hlo : P.IsStrictlyGE a) (_hhi : P.IsStrictlyLE b)
          (_ht : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n))
          (hP : IsPerfectRingComplex (DerivedCategory.Q.obj P)),
        ∃ (k : DerivedCategory.Q.obj (moduleHomComplex P (coefficient R)) ≅
            ((coefficientDerivedDual R).obj (op (DerivedCategory.Q.obj P))))
          (l : DerivedCategory.Q.obj (moduleHomComplex ((E f).obj P) (coefficient S)) ≅
            ((coefficientDerivedDual S).obj (op (DerivedCategory.Q.obj ((E f).obj P))))),
          (Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P (coefficient R)) ≫
              DerivedCategory.Q.map (ev R P) =
            DerivedCategory.Q.obj P ◁ k.hom ≫
              (ihom.ev (DerivedCategory.Q.obj P)).app (𝟙_ (D R)) ≫
                Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat R))) ∧
          (Functor.LaxMonoidal.μ DerivedCategory.Q ((E f).obj P)
              (moduleHomComplex ((E f).obj P) (coefficient S)) ≫ DerivedCategory.Q.map (ev S ((E
                f).obj P)) =
            DerivedCategory.Q.obj ((E f).obj P) ◁ l.hom ≫
              (ihom.ev (DerivedCategory.Q.obj ((E f).obj P))).app (𝟙_ (D S)) ≫
                Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat S))) ∧
          (B f).map k.inv ≫ modelMap f (moduleHomComplex P (coefficient R)) ≫
              DerivedCategory.Q.map (beta f P) ≫ l.hom ≫
              (MonoidalClosed.pre (modelMap f P)).app (𝟙_ (D S)) =
            (delta f (DerivedCategory.Q.obj P) hP).hom) ∧
      (∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
          (P : D.{u, u} R) (hP : IsPerfectRingComplex P),
        (B f).map ((ihom.ev P).app (𝟙_ (D R))) ≫ (coherenceData.unit f).hom =
          (coherenceData.tensor f P ((coefficientDerivedDual R).obj (op P))
            hP (dualPerfect R P hP)).hom ≫
              (B f).obj P ◁ (delta f P hP).hom ≫
                (ihom.ev ((B f).obj P)).app (𝟙_ (D S))) ∧
      (∀ (R : CommRingCat.{u}) (P : D.{u, u} R) (hP : IsPerfectRingComplex P),
        (delta (𝟙 R) P hP).hom =
          (coherenceData.identity R ((coefficientDerivedDual R).obj (op P)) (dualPerfect R P
            hP)).hom ≫
            (MonoidalClosed.pre (coherenceData.identity R P hP).hom).app (𝟙_ (D R))) ∧
      (∀ {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
          (P : D.{u, u} R) (hP : IsPerfectRingComplex P),
        (B g).map (delta f P hP).hom ≫
            (delta g ((B f).obj P) (coherenceData.preserves f P hP)).hom =
          (coherenceData.comp f g ((coefficientDerivedDual R).obj (op P)) (dualPerfect R P
            hP)).hom ≫
            (delta (f ≫ g) P hP).hom ≫
            (MonoidalClosed.pre (coherenceData.comp f g P hP).hom).app (𝟙_ (D T))) ∧
      (∀ (R : CommRingCat.{u}) (U : Submonoid R)
          (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (v : P ⟶ Q),
        QuasiIso v → QuasiIso
          (((ModuleCat.localizedModuleFunctor U).mapHomologicalComplex (.up ℤ)).map v)) ∧
      (∀ (R : CommRingCat.{u}) (U : Submonoid R),
        ∃ l : E (CommRingCat.ofHom (algebraMap R (Localization U))) ≅
            (ModuleCat.localizedModuleFunctor U).mapHomologicalComplex (.up ℤ),
          (∀ (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (x : P.X n),
            (l.hom.app P).f n ((1 : Localization U) ⊗ₜ[R] x) =
              (P.X n).localizedModuleMkLinearMap U x) ∧
          ∃ eta : ∀ P : CochainComplex (ModuleCat.{u} R) ℤ,
            ((ModuleCat.localizedModuleFunctor U).mapHomologicalComplex (.up ℤ)).obj
                (moduleHomComplex P (coefficient R)) ⟶
              moduleHomComplex
                (((ModuleCat.localizedModuleFunctor U).mapHomologicalComplex (.up ℤ)).obj P)
                (coefficient (CommRingCat.of (Localization U))),
            (∀ P : CochainComplex (ModuleCat.{u} R) ℤ,
              eta P = l.inv.app (moduleHomComplex P (coefficient R)) ≫
                beta (CommRingCat.ofHom (algebraMap R (Localization U))) P ≫
                  pre (CommRingCat.of (Localization U)) (l.inv.app P)) ∧
            (∀ (P : CochainComplex (ModuleCat.{u} R) ℤ) (p j : ℤ) (h : p + j = 0)
                (z : (moduleHomComplex P (coefficient R)).X j) (x : P.X p) (s t : U),
              (((eta P).f j
                  (@id (((moduleHomComplex P (coefficient R)).X j).localizedModule U)
                    (IsLocalizedModule.mk'
                      (((moduleHomComplex P (coefficient R)).X j).localizedModuleMkLinearMap U)
                      z s))).v p 0 h)
                  (@id ((P.X p).localizedModule U)
                    (IsLocalizedModule.mk' ((P.X p).localizedModuleMkLinearMap U) x t)) =
                IsLocalization.mk' (Localization U) (@id R ((z.v p 0 h) x)) (s * t))) := by
  classical
  have hevs : ∀ R : CommRingCat.{u}, ∃ ev : ∀ P : CochainComplex (ModuleCat.{u} R) ℤ,
      P ⊗ moduleHomComplex P (coefficient R) ⟶ coefficient R,
      ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ) (p j : ℤ)
        (x : P.X p) (z : (moduleHomComplex P (coefficient R)).X j),
        (ev P).f (p + j)
          (HomologicalComplex.ιTensorObj P (moduleHomComplex P (coefficient R)) p j
            (p + j) rfl (x ⊗ₜ[R] z)) = (p * j).negOnePow • (z.v p (p + j) rfl) x := by
    intro R
    obtain ⟨_, ev, _, hev, _⟩ := projective_hom_evaluation_model R
    exact ⟨fun P ↦ ev P (coefficient R), fun P ↦ hev P (coefficient R)⟩
  choose ev hev using hevs
  have hterms : ∀ {R S : CommRingCat.{u}} (f : R ⟶ S)
      (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
      (_ : P.IsStrictlyGE a) (_ : P.IsStrictlyLE b)
      (ht : ∀ n : ℤ, Module.Projective R (P.X n) ∧ Module.Finite R (P.X n)),
      IsIso (betaMap f P) ∧
      (∀ n, Module.Projective S (((E f).obj P).X n) ∧
        Module.Finite S (((E f).obj P).X n)) ∧
      (∀ n, Module.Projective R ((moduleHomComplex P (coefficient R)).X n) ∧
        Module.Finite R ((moduleHomComplex P (coefficient R)).X n)) ∧
      (∀ n, Module.Projective S ((moduleHomComplex ((E f).obj P) (coefficient S)).X n) ∧
        Module.Finite S ((moduleHomComplex ((E f).obj P) (coefficient S)).X n)) := by
    intro R S f P a b _ _ ht
    exact ⟨beta_isIso f P ht, scalar_terms f P ht, dualX_finite_projective R P ht,
      dualX_finite_projective S ((E f).obj P) (scalar_terms f P ht)⟩
  obtain ⟨delta, hnat, hmodel, heval, hid, hcomp⟩ :=
    perfect_dual_derived_transport ev (fun f P ↦ betaMap f P)
      dual_perfect hev (beta_evaluation ev hev) scalar_terms dualX_finite_projective
  refine ⟨(fun _ ↦ preMap), ev, (fun f P ↦ betaMap f P), dual_perfect, delta,
    (fun _ _ _ v _ _ _ _ ↦ preMap_v v _ _ _ _ _), hev, betaMap_apply,
    beta_evaluation ev hev, hterms, beta_naturality, beta_identity, beta_comp,
    beta_tower_apply, hnat, hmodel, heval, hid, hcomp, localization_quasiIso, ?_⟩
  intro R U
  let l := NatIso.mapHomologicalComplex (localizationModuleIso R U) (.up ℤ)
  let eta (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
    l.inv.app (moduleHomComplex P (coefficient R)) ≫
      betaMap (CommRingCat.ofHom (algebraMap R (Localization U))) P ≫ preMap (l.inv.app P)
  refine ⟨l, fun P n x ↦ localizationModuleIso_one R U (P.X n) x,
    eta, fun _ ↦ rfl, ?_⟩
  intro P p j h z x s t
  change (((preMap (l.inv.app P)).f j
    ((betaMap (CommRingCat.ofHom (algebraMap R (Localization U))) P).f j
      ((localizationModuleIso R U).inv.app ((moduleHomComplex P (coefficient R)).X j)
        (@id (((moduleHomComplex P (coefficient R)).X j).localizedModule U)
          (IsLocalizedModule.mk'
            (((moduleHomComplex P (coefficient R)).X j).localizedModuleMkLinearMap U) z s))))).v
            p 0 h) (@id ((P.X p).localizedModule U)
      (IsLocalizedModule.mk' ((P.X p).localizedModuleMkLinearMap U) x t)) = _
  rw [preMap_v (R := CommRingCat.of (Localization U))]
  change ((betaMap (CommRingCat.ofHom (algebraMap R (Localization U))) P).f j
    ((localizationModuleIso R U).inv.app ((moduleHomComplex P (coefficient R)).X j)
      (@id (((moduleHomComplex P (coefficient R)).X j).localizedModule U)
        (IsLocalizedModule.mk'
          (((moduleHomComplex P (coefficient R)).X j).localizedModuleMkLinearMap U) z s)))).v
          p 0 h ((localizationModuleIso R U).inv.app (P.X p)
            (@id ((P.X p).localizedModule U)
      (IsLocalizedModule.mk' ((P.X p).localizedModuleMkLinearMap U) x t))) = _
  rw [localizationModuleIso_inv_mk, localizationModuleIso_inv_mk, betaMap_apply]
  change algebraMap R (Localization U) ((z.v p 0 h) x) *
    IsLocalization.mk' (Localization U) 1 s * IsLocalization.mk' (Localization U) 1 t = _
  rw [mul_assoc, ← IsLocalization.mk'_mul, one_mul,
    ← IsLocalization.mk'_eq_mul_mk'_one]
  rfl

end CochainComplex.PerfectDualScalar
