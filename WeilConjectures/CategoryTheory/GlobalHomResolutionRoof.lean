/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # The ordinary-to-resolved global Hom roof

Source: Stacks Project, dga.tex, Example 09L9 (example-category-complexes),
derived.tex, Lemma 070I (lemma-K-injective), and sites-cohomology.tex, Section 0B6E.
(blueprint: lem-sf-global-hom-resolution-roof)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.HomComplex

namespace CategoryTheory

variable (B : Type v) [CommRing B] {A : Type u} [Category.{v} A] [Abelian A] [Linear B A]

/-- Product Hom with scalars retained, using Mathlib's cochains and exact signed differential.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHom (X Y : CochainComplex A ℤ) : CochainComplex (ModuleCat.{v} B) ℤ where
  X n := ModuleCat.of B (Cochain X Y n)
  d n m := ModuleCat.ofHom (δ_hom B X Y n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_shape n m h z
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_δ n m k z

/-- The degreewise pre/postcomposition map on the existing linear cochains.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomMapTerm {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℤ) :
    (globalLinearHom B X Y).X n ⟶ (globalLinearHom B X' Y').X n :=
  ModuleCat.ofHom
    { toFun := fun f ↦ (Cochain.ofHom a).comp (f.comp (Cochain.ofHom b) (add_zero n))
        (zero_add n)
      map_add' := by intros; simp
      map_smul' := by intros; simp }

/-- The pre/postcomposition maps commute with the Hom differential.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof).
Proof: expand both differentials as `d_Y f - (-1)^n f d_X`, and use the chain-map
identities for `a` and `b`. The two expressions agree componentwise. -/
theorem globalLinearHomMap_comm {X X' Y Y' : CochainComplex A ℤ}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n m : ℤ) :
    globalLinearHomMapTerm B a b n ≫ (globalLinearHom B X' Y').d n m =
      (globalLinearHom B X Y).d n m ≫ globalLinearHomMapTerm B a b m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ n m ((Cochain.ofHom a).comp
      (z.comp (Cochain.ofHom b) (add_zero n)) (zero_add n)) =
    (Cochain.ofHom a).comp
      ((δ n m z).comp (Cochain.ofHom b) (add_zero m)) (zero_add m)
  rw [δ_ofHom_comp, δ_comp_ofHom]

/-- Actual pre/postcomposition chain map, with its prescribed component formula.
Source: Stacks 09L9 (blueprint: lem-sf-global-hom-resolution-roof). -/
def globalLinearHomMap {X X' Y Y' : CochainComplex A ℤ} (a : X' ⟶ X) (b : Y ⟶ Y') :
    globalLinearHom B X Y ⟶ globalLinearHom B X' Y' where
  f := globalLinearHomMapTerm B a b
  comm' n m _ := globalLinearHomMap_comm B a b n m

/-- A resolution is only a complex and its given quasi-isomorphism, with the usual
K-injectivity predicate; no linear or functorial choice is part of this input.
Source: Stacks 070I (blueprint: lem-sf-global-hom-resolution-roof). -/
structure GlobalHomResolution (X : CochainComplex A ℤ) where
  I : CochainComplex A ℤ
  ι : X ⟶ I
  injective : I.IsKInjective
  quasiIso : QuasiIso ι

attribute [instance] GlobalHomResolution.injective GlobalHomResolution.quasiIso

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{t} (ModuleCat.{v} B)]

end CategoryTheory
