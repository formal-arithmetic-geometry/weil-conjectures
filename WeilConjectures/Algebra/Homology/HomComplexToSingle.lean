/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Signed dual and Hom into a single sheaf

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-to-single).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R : Sheaf J CommRingCat.{u}}

private lemma homObjMap_zero_source {M M' N : SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (0 : M' ⟶ M) (𝟙 N) = 0 := by
  exact (((SheafOfModules.homFunctor R).flip.obj N).map_zero (op M) (op M'))

/-- The signed dual differential squares to zero.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: def-sc-signed-sheaf-dual-complex).
Proof: the two signs factor out, and precomposition reverses composition.
The remaining composite is precomposition by two successive differentials of L,
which is zero by the complex identity. -/
theorem signedSheafDual_d_comp_d
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (n : ℤ) :
    (-(n.negOnePow) • SheafOfModules.homObjMap (L.d (-(n + 1)) (-n)) (𝟙 N)) ≫
      (-((n + 1).negOnePow) •
        SheafOfModules.homObjMap (L.d (-((n + 1) + 1)) (-(n + 1))) (𝟙 N)) = 0 := by
  rw [Linear.units_smul_comp, Linear.comp_units_smul]
  simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp,
    HomologicalComplex.d_comp_d, homObjMap_zero_source, smul_zero]

/-- The signed internal sheaf dual of an integer cochain complex.
It has terms Hom(L^(-n), N) and differential -(-1)^n times precomposition.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: def-sc-signed-sheaf-dual-complex). -/
noncomputable def signedSheafDualComplex
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ :=
  CochainComplex.of (fun n ↦ SheafOfModules.homObj (L.X (-n)) N)
    (fun n ↦ -(n.negOnePow) • SheafOfModules.homObjMap (L.d (-(n + 1)) (-n)) (𝟙 N))
    (signedSheafDual_d_comp_d L N)

private lemma homObjMap_zero_target {M N N' : SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (f : M ⟶ M) :
    SheafOfModules.homObjMap (R := R) f (0 : N ⟶ N') = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
  ext W x
  rfl

private lemma isIso_dependent {D : Type*} [Category D] {A : D} {B : ℤ → D}
    {k : ℤ} (π : ∀ q, k = q → (A ⟶ B q)) {q : ℤ} (hq : k = q)
    (hi : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact hi


end CategoryTheory
