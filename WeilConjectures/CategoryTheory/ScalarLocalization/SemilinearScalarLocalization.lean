/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-!
# Semilinear functors under raw scalar localization

Source: Weil conjectures blueprint, main-20261015, `sec-smooth-purity`,
`sk-lem-sp-field-extension/prop-pur-rational-purity-transitivity-summands.proof.md`,
finite-extension sentence (blueprint: lem-pur-semilinear-scalar-localization).

The construction uses the existing scalar-first tensor Hom modules. The unique additive
Hom extension specifies its data completely, so choosing that extension postpones only
proofs. Functor, transformation, coherence and exactness statements below express the
successive clauses of the node. HEq in coherence laws only transports equal endpoints;
it never replaces an equality by an isomorphism.
-/

@[expose] public section

universe r s q u v w x y z

open TensorProduct CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.ScalarLocalization

variable {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type w} [Category.{x} D] [Preadditive D] [Linear S D]

variable (t : R) (b : S) (φ : R →+* S)
  (h : IsUnit (algebraMap S (Localization.Away b) (φ t)))

@[simp] private theorem extensionHom_tmul (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) (K L : C) (a : Localization.Away t) (f : K ⟶ L) :
    extensionHom t b φ h F hF K L (a ⊗ₜ[R] f) =
      coefficientMap t b φ h a ⊗ₜ[S] F.map f :=
  Classical.choose_spec (existsUnique_semilinearHom t b φ h F hF K L).exists a f

variable {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
  (hF : IsSemilinear φ F) (hG : IsSemilinear φ G) (hH : IsSemilinear φ H)

section Composition

variable {T : Type q} [CommRing T] {E : Type y} [Category.{z} E]
  [Preadditive E] [Linear T E] (c : T) (ψ : S →+* T)
  (hψ : IsUnit (algebraMap T (Localization.Away c) (ψ b)))

end Composition

section Triangulated

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [triC : IsTriangulated C] [(shiftFunctor C (1 : ℤ)).Linear R]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [triD : IsTriangulated D] [(shiftFunctor D (1 : ℤ)).Linear S]
  [HasZeroObject (ScalarLocalization R C t)] [HasShift (ScalarLocalization R C t) ℤ]
  [∀ n : ℤ, (shiftFunctor (ScalarLocalization R C t) n).Additive]
  [Pretriangulated (ScalarLocalization R C t)] [triLC : IsTriangulated (ScalarLocalization R C t)]
  [HasZeroObject (ScalarLocalization S D b)] [HasShift (ScalarLocalization S D b) ℤ]
  [∀ n : ℤ, (shiftFunctor (ScalarLocalization S D b) n).Additive]
  [Pretriangulated (ScalarLocalization S D b)] [triLD : IsTriangulated (ScalarLocalization S D b)]
  [(localization R C t).CommShift ℤ] [(localization S D b).CommShift ℤ]
  (hshiftC : shiftFunctor (ScalarLocalization R C t) (1 : ℤ) =
    map R C t (shiftFunctor C (1 : ℤ)))
  (hshiftD : shiftFunctor (ScalarLocalization S D b) (1 : ℤ) =
    map S D b (shiftFunctor D (1 : ℤ)))
  (hQC : ∀ K : C, HEq (((localization R C t).commShiftIso (1 : ℤ)).hom.app K)
    (𝟙 ((localization R C t).obj ((shiftFunctor C (1 : ℤ)).obj K))))
  (hQD : ∀ K : D, HEq (((localization S D b).commShiftIso (1 : ℤ)).hom.app K)
    (𝟙 ((localization S D b).obj ((shiftFunctor D (1 : ℤ)).obj K))))
  (hdistC : ∀ Δ : Triangle (ScalarLocalization R C t),
    Δ ∈ distTriang (ScalarLocalization R C t) ↔
      ∃ Δ₀ : Triangle C, Δ₀ ∈ distTriang C ∧
        Nonempty (Δ ≅ (localization R C t).mapTriangle.obj Δ₀))
  (hdistD : ∀ Δ : Triangle (ScalarLocalization S D b),
    Δ ∈ distTriang (ScalarLocalization S D b) ↔
      ∃ Δ₀ : Triangle D, Δ₀ ∈ distTriang D ∧
        Nonempty (Δ ≅ (localization S D b).mapTriangle.obj Δ₀))

end Triangulated

end CategoryTheory.ScalarLocalization
