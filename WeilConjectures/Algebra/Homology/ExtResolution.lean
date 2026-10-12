/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.Additive

/-!
# Ext classes of cocycles on a resolution

Let `K` be a chain complex in an abelian category, augmented by `ε : K₀ ⟶ A`, which is a
resolution of `A`: the augmented complex `⋯ ⟶ K₁ ⟶ K₀ ⟶ A ⟶ 0` is exact
(`ChainComplex.IsResolution`). The terms of `K` need not be projective. Write
`B₀ = A` and `B_{n + 1} = ker(Kₙ ⟶ Bₙ)`, so that there are short exact sequences
`0 ⟶ B_{n + 1} ⟶ Kₙ ⟶ Bₙ ⟶ 0`, with extension classes `eₙ ∈ Ext¹(Bₙ, B_{n + 1})`. A cocycle
`φ : K_q ⟶ F` (i.e. `d ≫ φ = 0`) factors through `K_q ⟶ B_q` and defines the class
`e₀ ⋯ e_{q - 1} φ̄ ∈ Ext^q(A, F)` (`ChainComplex.IsResolution.cocycleClass`).

These classes vanish on coboundaries, are natural in `F` and in morphisms of resolutions, are
compatible with the connecting homomorphisms of short exact sequences and with exact functors, and
in degree `0` they identify `Hom(A, F)` with the cocycles `K₀ ⟶ F`.

When `K` is the free resolution of the constant sheaf attached to a hypercover, these are the
classes of hypercover cocycles in sheaf cohomology.
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory Limits Abelian

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- `K` augmented by `ε : K₀ ⟶ A` is a resolution of `A`: `⋯ ⟶ K₁ ⟶ K₀ ⟶ A ⟶ 0` is exact. -/
structure IsResolution (K : ChainComplex 𝒜 ℕ) {A : 𝒜} (ε : K.X 0 ⟶ A) : Prop where
  d_comp : K.d 1 0 ≫ ε = 0
  exactAt (n : ℕ) : K.ExactAt (n + 1)
  exact_zero : (ShortComplex.mk (K.d 1 0) ε d_comp).Exact
  epi : Epi ε

namespace IsResolution

variable {K : ChainComplex 𝒜 ℕ} {A : 𝒜} {ε : K.X 0 ⟶ A} [HasExt.{w} 𝒜]

/-- The class in `Ext^q(A, F)` of a cocycle `φ : K_q ⟶ F` of a resolution `K` of `A`. -/
noncomputable def cocycleClass (hK : IsResolution K ε) (q : ℕ) {F : 𝒜} (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0) :
    Ext A F q :=
  sorry

variable (hK : IsResolution K ε)
include hK

lemma cocycleClass_add (q : ℕ) {F : 𝒜} (φ ψ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0)
    (hψ : K.d (q + 1) q ≫ ψ = 0) :
    hK.cocycleClass q (φ + ψ) (by simp [hφ, hψ]) = hK.cocycleClass q φ hφ + hK.cocycleClass q ψ hψ :=
  sorry

/-- The class of a coboundary vanishes. -/
lemma cocycleClass_d (q : ℕ) {F : 𝒜} (ψ : K.X q ⟶ F) :
    hK.cocycleClass (q + 1) (K.d (q + 1) q ≫ ψ) (by simp) = 0 :=
  sorry

/-- Naturality in the target. -/
lemma cocycleClass_comp (q : ℕ) {F G : 𝒜} (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0)
    (g : F ⟶ G) :
    hK.cocycleClass q (φ ≫ g) (by simp [reassoc_of% hφ]) =
      (hK.cocycleClass q φ hφ).comp (Ext.mk₀ g) (add_zero q) :=
  sorry

/-- Naturality in the resolution: the classes are compatible with morphisms of resolutions of `A`
(which need not be unique up to homotopy, since the terms need not be projective). -/
lemma cocycleClass_naturality {K' : ChainComplex 𝒜 ℕ} {ε' : K'.X 0 ⟶ A}
    (hK' : IsResolution K' ε') (f : K' ⟶ K) (hf : f.f 0 ≫ ε = ε') (q : ℕ) {F : 𝒜}
    (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0) :
    hK'.cocycleClass q (f.f q ≫ φ) (by rw [← HomologicalComplex.Hom.comm_assoc, hφ, comp_zero]) =
      hK.cocycleClass q φ hφ :=
  sorry

/-- Compatibility with connecting homomorphisms: if `φ' : K_q ⟶ S.X₂` lifts a cocycle
`φ' ≫ S.g : K_q ⟶ S.X₃` and `ψ : K_{q + 1} ⟶ S.X₁` satisfies `ψ ≫ S.f = d ≫ φ'`, then `ψ` is a
cocycle whose class is the image of the class of `φ' ≫ S.g` under the connecting map. -/
lemma cocycleClass_extClass {S : ShortComplex 𝒜} (hS : S.ShortExact) (q : ℕ)
    (φ' : K.X q ⟶ S.X₂) (hφ' : K.d (q + 1) q ≫ φ' ≫ S.g = 0) (ψ : K.X (q + 1) ⟶ S.X₁)
    (hψ : ψ ≫ S.f = K.d (q + 1) q ≫ φ') (hψ' : K.d (q + 2) (q + 1) ≫ ψ = 0) :
    hK.cocycleClass (q + 1) ψ hψ' =
      (hK.cocycleClass q (φ' ≫ S.g) hφ').comp hS.extClass rfl :=
  sorry

/-- In degree `0`, the classes of the cocycles `K₀ ⟶ F` are exactly the elements of
`Ext⁰(A, F) = Hom(A, F)`, each attained exactly once. -/
lemma bijective_cocycleClass_zero (F : 𝒜) :
    Function.Bijective (fun φ : {φ : K.X 0 ⟶ F // K.d 1 0 ≫ φ = 0} ↦
      hK.cocycleClass 0 φ.1 φ.2) :=
  sorry

/-- An exact functor maps resolutions to resolutions. -/
lemma map {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ] (G : 𝒜 ⥤ ℬ) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    ChainComplex.IsResolution ((G.mapHomologicalComplex _).obj K) (G.map ε) :=
  sorry

/-- Exact functors map classes of cocycles to classes of cocycles. -/
lemma mapExt_cocycleClass {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ] [HasExt.{w} ℬ]
    (G : 𝒜 ⥤ ℬ) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (q : ℕ) {F : 𝒜} (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0) :
    (hK.cocycleClass q φ hφ).mapExactFunctor G =
      (hK.map G).cocycleClass q (G.map φ)
        (by simp [← G.map_comp, hφ]) :=
  sorry

end IsResolution

end ChainComplex
