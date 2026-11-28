/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Natural endomorphisms of constant ring sheaves

A natural endomorphism of the underlying sheaves of sets of the constant ring sheaves
`A ↦ (constantSheaf J CommRingCat).obj A`, which is additive and unital on sections, is the
identity (`CategoryTheory.constantSheaf_forget_natTrans_eq_id`).

## Implementation details

Naturality along evaluations of the polynomial ring `ℤ[X]` reduces the claim to the image `p`
of the variable `X`. Locally `p` comes from a polynomial `q`, and naturality together with
additivity and unitality give `q(2X) = 2q` and `q(1) = 1` wherever the constant presheaf maps
injectively to the sheaf, forcing `q = X`. Where it does not, the empty sieve covers and all
sections agree.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite Polynomial

namespace CategoryTheory



/-- An integer polynomial with `q(2X) = 2q` and `q(1) = 1` is `X`. -/
private theorem polynomial_eq_X_of_comp (q : ℤ[X]) (h₂ : q.comp (C 2 * X) = 2 * q)
    (h₁ : q.eval 1 = 1) : q = X := by
  have hc (n : ℕ) (hn : n ≠ 1) : q.coeff n = 0 := by
    have := congrArg (fun p ↦ p.coeff n) h₂
    simp only [comp_C_mul_X_coeff] at this
    rw [show (2 : ℤ[X]) = C 2 by simp, coeff_C_mul] at this
    have h2 : (2 : ℤ) ^ n ≠ 2 := by
      intro h
      rcases n with _ | _ | n
      · simp at h
      · exact hn rfl
      · have : (2 : ℤ) ^ (n + 2) ≥ 4 := by
          calc (2 : ℤ) ^ (n + 2) = 4 * 2 ^ n := by ring
            _ ≥ 4 * 1 := by gcongr; exact one_le_pow₀ (by norm_num)
            _ = 4 := by ring
        omega
    have : q.coeff n * (2 ^ n - 2) = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) h2
  have hq : q = C (q.coeff 1) * X := by
    ext n
    rw [coeff_C_mul_X]
    split_ifs with hn
    · rw [hn]
    · exact hc n hn
  rw [hq] at h₁ ⊢
  simp only [eval_mul, eval_C, eval_X, mul_one] at h₁
  rw [h₁, C_1, one_mul]


variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Sections of a ring sheaf agreeing on a covering sieve are equal. -/
private theorem sections_ext (R : Sheaf J CommRingCat.{u}) {V : C} (S : Sieve V)
    (hS : S ∈ J V) (x y : R.obj.obj (op V))
    (h : ∀ ⦃W : C⦄ (f : W ⟶ V), S f → R.obj.map f.op x = R.obj.map f.op y) : x = y :=
  (((isSheaf_iff_isSheaf_of_type J _).1
    ((sheafCompose J (forget CommRingCat.{u})).obj R).property) S hS).isSeparatedFor.ext h

/-- The canonical map from the coefficient ring to sections of the constant sheaf. -/
private abbrev constIncl (A : CommRingCat.{u}) (V : Cᵒᵖ) :
    A ⟶ ((constantSheaf J CommRingCat.{u}).obj A).obj.obj V :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app V

/-- The inclusion of constants is natural in the coefficient ring. -/
private theorem constIncl_map {A B : CommRingCat.{u}} (α : A ⟶ B) (V : Cᵒᵖ) (a : A) :
    ((constantSheaf J CommRingCat.{u}).map α).hom.app V (constIncl (J := J) A V a) =
      constIncl B V (α a) := by
  have := congrArg (fun t ↦ t.app V a)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map α))
  exact this.symm

/-- The inclusion of constants commutes with restriction. -/
private theorem constIncl_restrict (A : CommRingCat.{u}) {V W : Cᵒᵖ} (f : V ⟶ W) (a : A) :
    ((constantSheaf J CommRingCat.{u}).obj A).obj.map f (constIncl (J := J) A V a) =
      constIncl A W a := by
  have := congrArg (fun t ↦ t a)
    ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).naturality f)
  exact this.symm


/-- The polynomial ring in one variable, as a commutative ring in universe `u`. -/
private abbrev polyRing : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ[X])

/-- Substitution of `r` for the variable. -/
private abbrev polySubst (r : ℤ[X]) : polyRing.{u} ⟶ polyRing.{u} :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((eval₂RingHom Polynomial.C r).comp ULift.ringEquiv.toRingHom))

/-- Evaluation at an element `a`. -/
private abbrev polyEval (A : CommRingCat.{u}) (a : A) : polyRing.{u} ⟶ A :=
  CommRingCat.ofHom ((eval₂RingHom (Int.castRingHom A) a).comp ULift.ringEquiv.toRingHom)

variable (J) in
/-- A natural endomorphism of the underlying sheaves of sets of the constant ring sheaves
which is additive and unital on sections is the identity. -/
theorem constantSheaf_forget_natTrans_eq_id
    (ψ : constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u}) ⟶
      constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u}))
    (hadd : ∀ (A : CommRingCat.{u}) (V : Cᵒᵖ)
      (x y : ((constantSheaf J CommRingCat.{u}).obj A).obj.obj V),
      @id (((constantSheaf J CommRingCat.{u}).obj A).obj.obj V) ((ψ.app A).hom.app V (x + y)) =
        @id (((constantSheaf J CommRingCat.{u}).obj A).obj.obj V) ((ψ.app A).hom.app V x) +
          @id (((constantSheaf J CommRingCat.{u}).obj A).obj.obj V) ((ψ.app A).hom.app V y))
    (hone : ∀ (A : CommRingCat.{u}) (V : Cᵒᵖ),
      @id (((constantSheaf J CommRingCat.{u}).obj A).obj.obj V)
        ((ψ.app A).hom.app V (1 : ((constantSheaf J CommRingCat.{u}).obj A).obj.obj V)) = 1) :
    ψ = 𝟙 _ := by
  dsimp only [id] at hadd hone
  have hψ {A B : CommRingCat.{u}} (α : A ⟶ B) (V : Cᵒᵖ) (x) :
      (ψ.app B).hom.app V (((constantSheaf J CommRingCat.{u}).map α).hom.app V x) =
        ((constantSheaf J CommRingCat.{u}).map α).hom.app V ((ψ.app A).hom.app V x) :=
    congrArg (fun t ↦ t.hom.app V x) (ψ.naturality α)
  have hres (A : CommRingCat.{u}) {V W : Cᵒᵖ} (f : V ⟶ W) (x) :
      (ψ.app A).hom.app W (((constantSheaf J CommRingCat.{u}).obj A).obj.map f x) =
        ((constantSheaf J CommRingCat.{u}).obj A).obj.map f ((ψ.app A).hom.app V x) :=
    congrArg (fun t ↦ t x) ((ψ.app A).hom.naturality f)
  -- The generic point `X` is fixed.
  have hX (V : Cᵒᵖ) : (ψ.app polyRing).hom.app V (constIncl polyRing V (ULift.up X)) =
      constIncl polyRing V (ULift.up X) := by
    apply sections_ext _ _
      (Presheaf.imageSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj polyRing))
        ((ψ.app polyRing).hom.app V (constIncl polyRing V (ULift.up X)) :
          ((constantSheaf J CommRingCat.{u}).obj polyRing).obj.obj V))
    rintro W f ⟨t, ht⟩
    change constIncl polyRing (op W) t = ((constantSheaf J CommRingCat.{u}).obj polyRing).obj.map
      f.op ((ψ.app polyRing).hom.app V (constIncl polyRing V (ULift.up X))) at ht
    rw [constIncl_restrict]
    rw [← hres, constIncl_restrict] at ht
    obtain ⟨q⟩ := t
    have hsub (r : ℤ[X]) : (ψ.app polyRing).hom.app (op W)
        (constIncl polyRing (op W) (ULift.up r)) =
          constIncl polyRing (op W) (ULift.up (q.comp r)) := by
      have h1 := constIncl_map (J := J) (polySubst r) (op W) (ULift.up X)
      have h2 : (polySubst r) (ULift.up X) = ULift.up r := by
        simp [polySubst, ULift.ringEquiv]
      rw [h2] at h1
      rw [← h1, hψ, ← ht, constIncl_map]
      rfl
    have e₂ := hsub (Polynomial.C 2 * X)
    rw [show (ULift.up (Polynomial.C 2 * X) : polyRing.{u}) =
        ULift.up X + ULift.up X by ext1; simp; ring, map_add, hadd, ← ht, ← map_add] at e₂
    have e₁ := hsub 1
    rw [show (ULift.up (1 : ℤ[X]) : polyRing.{u}) = 1 from rfl, map_one, hone,
      ← map_one (ConcreteCategory.hom (constIncl (J := J) polyRing (op W)))] at e₁
    apply sections_ext _ _ (J.intersection_covering
      (Presheaf.equalizerSieve_mem J (toSheafify J _) _ _ e₂)
      (Presheaf.equalizerSieve_mem J (toSheafify J _) _ _ e₁))
    rintro W' g ⟨hg₂, hg₁⟩
    change ULift.up q + ULift.up q = ULift.up (q.comp (Polynomial.C 2 * X)) at hg₂
    change (1 : polyRing.{u}) = ULift.up (q.comp 1) at hg₁
    have hq : q = X := by
      apply polynomial_eq_X_of_comp
      · have h := congrArg ULift.down hg₂
        rw [show Polynomial.C (2 : ℤ) = 2 by simp, two_mul q]
        simpa using h.symm
      · have h := congrArg ULift.down hg₁
        have h' : (1 : ℤ[X]) = ((eval 1 q : ℤ) : ℤ[X]) := by simpa [Polynomial.comp] using h
        exact_mod_cast h'.symm
    subst hq
    rw [← hres, constIncl_restrict, ← ht]
  -- Every inserted constant is fixed.
  have hconst (A : CommRingCat.{u}) (V : Cᵒᵖ) (a : A) :
      (ψ.app A).hom.app V (constIncl A V a) = constIncl A V a := by
    have h1 := constIncl_map (J := J) (polyEval A a) V (ULift.up X)
    have h2 : (polyEval A a) (ULift.up X) = a := by
      simp [polyEval, ULift.ringEquiv]
    rw [h2] at h1
    rw [← h1, hψ, hX]
  ext A : 2
  apply Sheaf.hom_ext
  ext V x
  apply sections_ext _ _ (Presheaf.imageSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj A))
    (x : ((constantSheaf J CommRingCat.{u}).obj A).obj.obj V))
  rintro W f ⟨t, ht⟩
  change constIncl A (op W) t = ((constantSheaf J CommRingCat.{u}).obj A).obj.map f.op x at ht
  change ((constantSheaf J CommRingCat.{u}).obj A).obj.map f.op
    ((ψ.app A).hom.app V x) = ((constantSheaf J CommRingCat.{u}).obj A).obj.map f.op x
  rw [← hres, ← ht, hconst]

end CategoryTheory
