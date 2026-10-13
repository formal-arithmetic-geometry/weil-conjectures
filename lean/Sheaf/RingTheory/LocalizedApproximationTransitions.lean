/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Localization.Defs

/-! # Base changes of localized approximation transitions

Source: Stacks Project, Algebra, Tag 00RC, first reduction paragraph, and Tag 00QX.
(blueprint: lem-weil-pbc-localized-approximation-transitions)
-/

@[expose] public section

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace Algebra

/-- Localization of transition ring and module base changes at compatible primes.

Source: Stacks Project, Algebra, Tag 00RC, first reduction paragraph, and Tag 00QX.
(blueprint: lem-weil-pbc-localized-approximation-transitions)

Proof:
1. Fix i ≤ j. The supplied pure-tensor ring isomorphism identifies B_j with
   B_i tensor over A_i A_j. Localizing the two tensor factors at q_i and its
   contraction to A_j gives B_i localized at q_i tensor over localized A_i
   localized A_j. The commuting localization squares identify its map to localized
   B_j with the product map on pure tensors. All denominators already inverted
   avoid q_j, by compatibility of the primes. Inverting the complement of the
   inverse image of the maximal ideal of localized B_j gives exactly localized B_j:
   the original tensor isomorphism and the localization universal properties give
   inverse fraction maps. This supplies W and the IsLocalization witness.
2. Localize the supplied module base-change equivalence. Tensor-localization
   compatibility first localizes the earlier module and then extends scalars to
   localized B_j. Both the resulting module and D^l_j are localizations of
   B_j tensor over B_i D_i at q_j. The IsLocalizedModule witnesses give their
   unique linear equivalence. On a tensor with denominator-one module numerator,
   the original pure-tensor formula and the compatibility of ζ with the transition
   give b tensor ζ_i(x) mapped to b ζ_j(D(f)(x)). Clear denominators in x to extend
   this to every localized x; this yields the stated pure-tensor formula.
These arguments are pointwise in the transition and do not use colimits or finiteness. -/
theorem localized_approximation_transition_base_change
    {Λ : Type u} [Preorder Λ]
    (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
    (D : Λ ⥤ AddCommGrpCat.{u}) [∀ i, Module (B.obj i) (D.obj i)]
    (q : ∀ i, Ideal (B.obj i)) [∀ i, (q i).IsPrime]
    (hq : ∀ (i j : Λ) (f : i ⟶ j), Ideal.comap (B.map f).hom (q j) = q i)
    (Aₗ Bₗ : Λ ⥤ CommRingCat.{u}) (Dₗ : Λ ⥤ AddCommGrpCat.{u})
    [∀ i, Module (Bₗ.obj i) (Dₗ.obj i)]
    (φ : ∀ i, Aₗ.obj i →+* Bₗ.obj i)
    (ρA : ∀ i, A.obj i →+* Aₗ.obj i) (ρB : ∀ i, B.obj i →+* Bₗ.obj i)
    (ζ : ∀ i, D.obj i →+ Dₗ.obj i)
    (hρA : ∀ i, letI := (ρA i).toAlgebra
      IsLocalization ((q i).comap (η.app i).hom).primeCompl (Aₗ.obj i))
    (hρB : ∀ i, letI := (ρB i).toAlgebra
      IsLocalization (q i).primeCompl (Bₗ.obj i))
    (hη : ∀ i, (ρB i).comp (η.app i).hom = (φ i).comp (ρA i))
    (hA : ∀ (i j : Λ) (f : i ⟶ j),
      (ρA j).comp (A.map f).hom = (Aₗ.map f).hom.comp (ρA i))
    (hB : ∀ (i j : Λ) (f : i ⟶ j),
      (ρB j).comp (B.map f).hom = (Bₗ.map f).hom.comp (ρB i))
    (hζ : ∀ (i j : Λ) (f : i ⟶ j) (x : D.obj i),
      ζ j ((D.map f).hom x) = (Dₗ.map f).hom (ζ i x))
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : Bₗ.obj i) (x : Dₗ.obj i),
      (Dₗ.map f).hom (b • x) = (Bₗ.map f).hom b • (Dₗ.map f).hom x)
    (hℓ : ∀ i, letI := Module.compHom (Dₗ.obj i) (ρB i)
      ∃ ℓ : D.obj i →ₗ[B.obj i] Dₗ.obj i,
        (∀ x, ℓ x = ζ i x) ∧ IsLocalizedModule (q i).primeCompl ℓ)
    (htB : ∀ (i j : Λ) (h : i ≤ j),
      letI := (η.app i).hom.toAlgebra
      letI := (A.map (homOfLE h)).hom.toAlgebra
      ∃ e : B.obj i ⊗[A.obj i] A.obj j ≃+* B.obj j,
        ∀ (x : B.obj i) (y : A.obj j),
          e (x ⊗ₜ[A.obj i] y) = (B.map (homOfLE h)).hom x * (η.app j).hom y)
    (htD : ∀ (i j : Λ) (h : i ≤ j),
      letI := (B.map (homOfLE h)).hom.toAlgebra
      ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
        ∀ (y : B.obj j) (x : D.obj i),
          e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x) :
    (∀ (i j : Λ) (f : i ⟶ j),
      letI := (φ i).toAlgebra
      letI := (Aₗ.map f).hom.toAlgebra
      ∃ (t : Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j →+* Bₗ.obj j)
        (W : Submonoid (Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j)),
        (∀ (b : Bₗ.obj i) (a : Aₗ.obj j),
          t (b ⊗ₜ[Aₗ.obj i] a) = (Bₗ.map f).hom b * φ j a) ∧
        (letI := t.toAlgebra; IsLocalization W (Bₗ.obj j))) ∧
    (∀ (i j : Λ) (f : i ⟶ j),
      letI := (Bₗ.map f).hom.toAlgebra
      ∃ e : Bₗ.obj j ⊗[Bₗ.obj i] Dₗ.obj i ≃ₗ[Bₗ.obj j] Dₗ.obj j,
        ∀ (b : Bₗ.obj j) (x : Dₗ.obj i),
          e (b ⊗ₜ[Bₗ.obj i] x) = b • (Dₗ.map f).hom x) := by sorry

end Algebra
