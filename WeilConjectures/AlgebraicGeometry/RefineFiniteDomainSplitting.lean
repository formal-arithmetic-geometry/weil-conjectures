/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.AlgebraicGeometry.RefinementLocalizationGeometry
import WeilConjectures.AlgebraicGeometry.ReducedProductLocalization

/-!
# Combining finitely many localizations of a finite domain decomposition
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct
open AlgebraicGeometry

/-- Combine specified principal opens on which the factors of an existing reduced algebra
product are universal homeomorphisms. This is localization and tensor-product bookkeeping;
the existence of those opens, and the product decomposition, are hypotheses. -/
theorem exists_refinement_of_finite_domain_splitting
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
    (c : A) (hc : c ≠ 0)
    (A' : Type u) [CommRing A'] [IsDomain A']
    [Algebra (Localization.Away c) A'] [Algebra A A']
    [IsScalarTower A (Localization.Away c) A']
    [Module.Finite (Localization.Away c) A'] [Algebra.Etale (Localization.Away c) A']
    (hcover : Surjective
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A'))))
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
    [∀ j, Algebra A' (D j)] [∀ j, Module.Finite A' (D j)]
    (hinj : ∀ j, Function.Injective (algebraMap A' (D j)))
    [∀ j, Algebra (Localization.Away c) (D j)]
    [∀ j, IsScalarTower (Localization.Away c) A' (D j)]
    (hsplit : letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := A')
      Nonempty (((B ⊗[A] A') ⧸ nilradical (B ⊗[A] A')) ≃ₐ[A'] (∀ j, D j)))
    (s : Fin r → Localization.Away c) (hs : ∀ j, s j ≠ 0)
    (hhomeo : ∀ j, (topologically IsHomeomorph).universally
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom (Localization.Away c) A' (D j))
          (AlgHom.id (Localization.Away c) (Localization.Away (s j)))).toRingHom))) :
    ∃ (d : A) (A'' : Type u) (_ : CommRing A'') (_ : Algebra (Localization.Away d) A'')
      (_ : Algebra A A'') (_ : IsScalarTower A (Localization.Away d) A''),
      d ≠ 0 ∧ Module.Finite (Localization.Away d) A'' ∧
        Algebra.Etale (Localization.Away d) A'' ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away d) A''))) ∧
        ∃ (E : Fin r → Type u) (_ : ∀ j, CommRing (E j))
          (_ : ∀ j, Algebra A'' (E j)),
          (∀ j, Module.Finite A'' (E j) ∧ IsDomain (E j) ∧
            Surjective (Spec.map (CommRingCat.ofHom (algebraMap A'' (E j)))) ∧
            (topologically IsHomeomorph).universally
              (Spec.map (CommRingCat.ofHom (algebraMap A'' (E j))))) ∧
          letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := A'')
          Nonempty (((B ⊗[A] A'') ⧸ nilradical (B ⊗[A] A'')) ≃ₐ[A''] (∀ j, E j)) := by
  classical
  let S := Localization.Away c
  have : IsDomain S := Localization.Away.isDomain hc
  let t : S := ∏ j, s j
  have ht : t ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hs j)
  let a : A := (IsLocalization.Away.sec c t).1
  have hassoc : Associated (algebraMap A S a) t :=
    IsLocalization.Away.associated_sec_fst c t
  have ha : a ≠ 0 := by
    intro h
    have hzero : algebraMap A S a = 0 := by simp [h]
    exact ht (hassoc.eq_zero_iff.mp hzero)
  let d := c * a
  have hd : d ≠ 0 := mul_ne_zero hc ha
  let T := Localization.Away (algebraMap A S a)
  have : IsLocalization.Away t T := IsLocalization.Away.of_associated hassoc
  let U := Localization.Away d
  let e : U ≃ₐ[A] T := IsLocalization.algEquiv (Submonoid.powers d) U T
  let : Algebra U T := e.toRingHom.toAlgebra
  have : IsScalarTower A U T := .of_algebraMap_eq fun z ↦ (e.commutes z).symm
  have hUT : Function.Bijective (algebraMap U T) := e.bijective
  let C := T ⊗[S] A'
  let : Algebra A' C := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower A A' C := .of_algebraMap_eq fun z ↦ by
    rw [IsScalarTower.algebraMap_apply A S A',
      ← IsScalarTower.algebraMap_apply S A' C,
      IsScalarTower.algebraMap_apply A S C]
  have : IsLocalization.Away (algebraMap S A' t) C :=
    IsLocalization.Away.tensorRight (R := S) (S := A') (A := T) (r := t)
  obtain ⟨hfinite, hetale, hsurj, hfactors⟩ :=
    refinement_localization_geometry S A' hcover r D hinj s hs hhomeo T U hUT
  have hproduct := reduced_product_localization A B A' r D hsplit
    (algebraMap S A' t) C
  refine ⟨d, C, inferInstance, inferInstance, inferInstance, inferInstance,
    hd, hfinite, hetale, hsurj, (fun j ↦ C ⊗[A'] D j), inferInstance,
    inferInstance, hfactors, hproduct⟩
