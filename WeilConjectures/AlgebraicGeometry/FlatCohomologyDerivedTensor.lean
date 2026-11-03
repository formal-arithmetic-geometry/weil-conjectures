/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveUnit

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Flat cohomology and derived tensor coefficients

Source: Stacks Project, more-algebra.tex, Tag 0H7Z, lemma-kunneth-spectral-sequence;
blueprint: lem-pur-flat-cohomology-derived-tensor.

This module states the canonical coefficient comparison obtained from the Kunneth spectral
sequence.  The proof is deferred: the four proof steps are the specialization to `M[0]`,
vanishing of higher Tor by flatness, identification of the edge map with the unit-normalized
pure-tensor map, and naturality in both variables.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The derived tensor map induced by a coefficient element `a : M`.
Source: Stacks Project, Tag 0H7Z; blueprint: lem-pur-flat-cohomology-derived-tensor. -/
def coefficientAction (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (M : ModuleCat.{u} R) (q : ℤ) (a : M) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj
        (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map
    ((ρ_ K).inv ≫
      ((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj K).map
        ((DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} R)).inv ≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
            (ModuleCat.ofHom (LinearMap.toSpanSingleton R M a))))

/-- The pure-tensor action function used to assemble the coefficient map: the value of
`coefficientAction` at the coefficient `a` on the cohomology class `x`.
Source: Stacks Project, Tag 0H7Z; blueprint: lem-pur-flat-cohomology-derived-tensor. -/
def coefficientActionFunction (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (M : ModuleCat.{u} R) (q : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K) (a : M) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj
      (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) : Type u) :=
  (coefficientAction R K M q a).hom x

/-- Bilinearity of the pure-tensor action; this is the postponed algebraic verification needed
by `TensorProduct.lift`.
Source: Stacks Project, Tag 0H7Z; blueprint: lem-pur-flat-cohomology-derived-tensor.
Proof: in `x` the action is the underlying map of a morphism of `ModuleCat R`, hence
additive and `R`-linear. In `a`, `a ↦ f_a = LinearMap.toSpanSingleton R M a` is `R`-linear,
and `singleFunctor`, `K ⊗ᴸ -` and `H^q` are `R`-linear on morphisms, so
`H^q(1_K ⊗ᴸ f_{a+a'}) = H^q(1_K ⊗ᴸ f_a) + H^q(1_K ⊗ᴸ f_{a'})` and
`H^q(1_K ⊗ᴸ f_{c a}) = c • H^q(1_K ⊗ᴸ f_a)`. -/
theorem coefficientActionFunction_bilinear
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (M : ModuleCat.{u} R) (q : ℤ) :
    (∀ x y a, coefficientActionFunction R K M q (x + y) a =
      coefficientActionFunction R K M q x a + coefficientActionFunction R K M q y a) ∧
    (∀ (c : R) x a, coefficientActionFunction R K M q (c • x) a =
      c • coefficientActionFunction R K M q x a) ∧
    (∀ x a a', coefficientActionFunction R K M q x (a + a') =
      coefficientActionFunction R K M q x a + coefficientActionFunction R K M q x a') ∧
    (∀ (c : R) x a, coefficientActionFunction R K M q x (c • a) =
      c • coefficientActionFunction R K M q x a) := by
  dsimp [coefficientActionFunction]
  constructor
  · intro x y a
    apply (coefficientAction R K M q a).hom.map_add
  constructor
  · intro c x a
    exact (coefficientAction R K M q a).hom.map_smul c x
  constructor
  · intro x a a'
    simp [coefficientAction, LinearMap.toSpanSingleton_add,
      ModuleCat.ofHom_add, Functor.map_add]
  · intro c x a
    change ((coefficientAction R K M q (c • a)).hom) x =
      c • ((coefficientAction R K M q a).hom x)
    have hs : ModuleCat.ofHom (LinearMap.toSpanSingleton R M (c • a)) =
          c • ModuleCat.ofHom (LinearMap.toSpanSingleton R M a) := by
      apply ModuleCat.hom_ext
      simp [LinearMap.toSpanSingleton_smul]
    simp [coefficientAction, hs, Functor.map_smul, MonoidalLinear.whiskerLeft_smul,
      Linear.comp_smul]


/-- The canonical coefficient map `β^q_{K,M} : H^q(K) ⊗_R M → H^q(K ⊗ᴸ_R M[0])`, assembled from
the pure-tensor actions, so that `β^q_{K,M}(x ⊗ a) = H^q(1_K ⊗ᴸ f_a)(x)`.
Source: Stacks Project, Tag 0H7Z; blueprint: lem-pur-flat-cohomology-derived-tensor. -/
def canonicalCoefficientMap (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (M : ModuleCat.{u} R) (q : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K) ⊗ M ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj
        (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := coefficientActionFunction_bilinear R K M q
  exact ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ R
    (coefficientActionFunction R K M q) h₁ h₂ h₃ h₄))

/-- The canonical coefficient map has the unit normalization on pure tensors.
Source: Stacks Project, Tag 0H7Z; blueprint: lem-pur-flat-cohomology-derived-tensor.
-/
theorem canonicalCoefficientMap_unit_normalization
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (M : ModuleCat.{u} R) (q : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K) (a : M) :
    (canonicalCoefficientMap R K M q).hom (x ⊗ₜ[R] a) =
      (coefficientAction R K M q a).hom x := by
  unfold canonicalCoefficientMap
  generalize coefficientActionFunction_bilinear R K M q = hb
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hb
  exact TensorProduct.lift.tmul x a

/-- The canonical coefficient maps are natural in `K`.
Source: Stacks Project, Tag 0H7Z; blueprint: lem-pur-flat-cohomology-derived-tensor.
-/
theorem canonicalCoefficientMap_natural_K
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K K' : DerivedCategory (ModuleCat.{u} R)) (M : ModuleCat.{u} R) (q : ℤ)
    (g : K ⟶ K') :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map g ⊗ₘ 𝟙 M) ≫
        canonicalCoefficientMap R K' M q =
      canonicalCoefficientMap R K M q ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map
          (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).map g).app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x a
  change (canonicalCoefficientMap R K' M q).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map g).hom x ⊗ₜ[R] a) =
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map
      (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).map g).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))).hom
          ((canonicalCoefficientMap R K M q).hom (x ⊗ₜ[R] a))
  rw [canonicalCoefficientMap_unit_normalization, canonicalCoefficientMap_unit_normalization]
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) q
  have he : H.map g ≫ coefficientAction R K' M q a =
      coefficientAction R K M q a ≫ H.map
        (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).map g).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
    dsimp only [coefficientAction, H]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp only [curriedTensor_obj_map, curriedTensor_map_app]
    rw [rightUnitor_inv_naturality_assoc, Category.assoc, ← whisker_exchange]
  exact congrArg (fun f ↦ f.hom x) he

/-- The canonical coefficient maps are natural in `M`.
Source: Stacks Project, Tag 0H7Z; blueprint: lem-pur-flat-cohomology-derived-tensor.
-/
theorem canonicalCoefficientMap_natural_M
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (M M' : ModuleCat.{u} R) (q : ℤ)
    (h : M ⟶ M') :
    ((𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj K)) ⊗ₘ h) ≫
        canonicalCoefficientMap R K M' q =
      canonicalCoefficientMap R K M q ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map
          (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj K).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map h)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x a
  change (canonicalCoefficientMap R K M' q).hom (x ⊗ₜ[R] h.hom a) =
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map
      (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj K).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map h))).hom
          ((canonicalCoefficientMap R K M q).hom (x ⊗ₜ[R] a))
  rw [canonicalCoefficientMap_unit_normalization, canonicalCoefficientMap_unit_normalization]
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) q
  have hf : ModuleCat.ofHom (LinearMap.toSpanSingleton R M' (h.hom a)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R M a) ≫ h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp [LinearMap.toSpanSingleton_apply]
  have he : coefficientAction R K M' q (h.hom a) =
      coefficientAction R K M q a ≫ H.map
        (((curriedTensor (DerivedCategory (ModuleCat.{u} R))).obj K).map (S.map h)) := by
    dsimp only [coefficientAction, H, S]
    rw [← Functor.map_comp]
    congr 1
    rw [hf, Functor.map_comp]
    simp only [curriedTensor_obj_map, Functor.map_comp, whiskerLeft_comp, Category.assoc]
  exact congrArg (fun f ↦ f.hom x) he

end AlgebraicGeometry.Etale
