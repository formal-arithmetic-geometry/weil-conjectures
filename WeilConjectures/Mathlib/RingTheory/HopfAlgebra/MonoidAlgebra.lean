/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import WeilConjectures.Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# The Hopf algebra of Laurent polynomials

The Laurent polynomial ring `R[T;T⁻¹]` is the Hopf algebra of the multiplicative group `𝔾ₘ`: the
monomials `T n` are group-like (`LaurentPolynomial.comul_T`, `LaurentPolynomial.counit_T`,
`LaurentPolynomial.antipode_T`). This file adds:

- `LaurentPolynomial.isGroupLikeElem_T`: the monomials are group-like.
- `LaurentPolynomial.algHomMulEquiv`: `R`-algebra homomorphisms `R[T;T⁻¹] → S`, with the
  convolution product, are the units of `S`, a homomorphism `φ` corresponding to the unit `φ(T)`.
- `LaurentPolynomial.groupLikeBialgHom`: the bialgebra homomorphism `R[T;T⁻¹] → A` sending `T` to
  a group-like element of a commutative Hopf algebra `A`.
- The ideal `(T n - 1)` is a Hopf ideal: it cuts out the group scheme `μ_n` of `n`-th roots of
  unity.

## Blueprint

- `def-sc-gm-ga`: the coordinate ring `k[t, t⁻¹]` of `𝐆_m`, with `m^*(t) = t ⊗ t`, `ε(t) = 1`,
  `i^*(t) = t⁻¹`, and the Hopf ideal `(t^n - 1)` of `μ_n`.
- `def-sc-general-linear-group`: the bialgebra homomorphism `t ↦ det`.
-/

@[expose] public section

open WithConv

namespace LaurentPolynomial

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The monomials `T n` of `R[T;T⁻¹]` are group-like. -/
theorem isGroupLikeElem_T (n : ℤ) : IsGroupLikeElem R (T n : R[T;T⁻¹]) where
  counit_eq_one := counit_T n
  comul_eq_tmul_self := comul_T n

variable {S : Type*} [Semiring S] [Algebra R S]

@[simp]
theorem lift_T (F : Multiplicative ℤ →* S) (n : ℤ) :
    AddMonoidAlgebra.lift R S ℤ F (T n) = F (Multiplicative.ofAdd n) :=
  (AddMonoidAlgebra.lift_single F n 1).trans (one_smul _ _)

/-- Two `R`-algebra homomorphisms out of `R[T;T⁻¹]` agreeing on `T` are equal. -/
theorem algHom_ext {f g : R[T;T⁻¹] →ₐ[R] S} (h : f (T 1) = g (T 1)) : f = g := by
  have hinv : f (T (-1)) = g (T (-1)) := by
    have hf : f (T (-1)) * f (T 1) = 1 := by rw [← map_mul, ← T_add]; simp
    have hg : g (T 1) * g (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
    calc f (T (-1)) = f (T (-1)) * (g (T 1) * g (T (-1))) := by rw [hg, mul_one]
      _ = g (T (-1)) := by rw [← mul_assoc, ← h, hf, one_mul]
  refine AddMonoidAlgebra.algHom_ext (fun n ↦ ?_) (Subsingleton.elim _ _)
  change f (T n) = g (T n)
  induction n using Int.induction_on with
  | zero => simp [T_zero]
  | succ i hi => rw [T_add, map_mul, map_mul, hi, h]
  | pred i hi => rw [sub_eq_add_neg, T_add, map_mul, map_mul, hi, hinv]

variable (R) (S : Type*) [CommSemiring S] [Algebra R S]

/-- `R`-algebra homomorphisms `R[T;T⁻¹] → S`, with the convolution product, are the units of `S`:
a homomorphism `φ` corresponds to the unit `φ(T)`, with inverse `φ(T⁻¹)`. In other words, the
`S`-points of `𝔾ₘ = Spec R[T;T⁻¹]` are the group `Sˣ`. -/
noncomputable def algHomMulEquiv : WithConv (R[T;T⁻¹] →ₐ[R] S) ≃* Sˣ where
  toFun φ := ((isUnit_T 1).map φ.ofConv).unit
  invFun u := toConv (AddMonoidAlgebra.lift R S ℤ ((Units.coeHom S).comp (zpowersHom Sˣ u)))
  left_inv φ := by
    ext1
    exact algHom_ext (by simp)
  right_inv u := by
    ext
    simp
  map_mul' φ ψ := by
    ext
    simp [T, -single_eq_C_mul_T]

variable {R S}

@[simp]
theorem coe_algHomMulEquiv (φ : WithConv (R[T;T⁻¹] →ₐ[R] S)) :
    (algHomMulEquiv R S φ : S) = φ.ofConv (T 1) :=
  rfl

@[simp]
theorem algHomMulEquiv_symm_apply_T (u : Sˣ) (n : ℤ) :
    ((algHomMulEquiv R S).symm u).ofConv (T n) = ((u ^ n : Sˣ) : S) := by
  simp [algHomMulEquiv]

end CommSemiring

section HopfAlgebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] {g : A}

/-- The monoid homomorphism `ℤ → A`, `n ↦ g ^ n`, for a group-like element `g` of a commutative
Hopf algebra `A` (the inverse of `g` being its antipode). -/
noncomputable def groupLikeZPowersHom (hg : IsGroupLikeElem R g) : Multiplicative ℤ →* A :=
  (Units.coeHom A).comp ((GroupLike.toUnits R).comp (zpowersHom _ ⟨g, hg⟩))

theorem isGroupLikeElem_groupLikeZPowersHom (hg : IsGroupLikeElem R g) (n : Multiplicative ℤ) :
    IsGroupLikeElem R (groupLikeZPowersHom hg n) :=
  ((zpowersHom (GroupLike R A) ⟨g, hg⟩) n).2

/-- The bialgebra homomorphism `R[T;T⁻¹] → A` sending `T` to a group-like element `g` of a
commutative Hopf algebra `A`. Dually, a morphism of affine group schemes `Spec A ⟶ 𝔾ₘ`.
(blueprint: `def-sc-general-linear-group`) -/
noncomputable def groupLikeBialgHom (hg : IsGroupLikeElem R g) : R[T;T⁻¹] →ₐc[R] A :=
  .ofAlgHom (AddMonoidAlgebra.lift R A ℤ (groupLikeZPowersHom hg))
    (by
      ext n
      simp [(isGroupLikeElem_groupLikeZPowersHom hg _).counit_eq_one])
    (by
      ext n
      simp [(isGroupLikeElem_groupLikeZPowersHom hg _).comul_eq_tmul_self])

@[simp]
theorem groupLikeBialgHom_T_one (hg : IsGroupLikeElem R g) : groupLikeBialgHom hg (T 1) = g := by
  simp [groupLikeBialgHom, groupLikeZPowersHom]

end HopfAlgebra

section CommRing

variable {R : Type*} [CommRing R]

/-- The ideal `(T n - 1)` of `R[T;T⁻¹]` is a Hopf ideal: it cuts out the group scheme `μ_n` of
`n`-th roots of unity in `𝔾ₘ`. (blueprint: `def-sc-gm-ga`) -/
instance isHopfIdeal_span_T_sub_one (n : ℤ) :
    (Ideal.span {(T n - 1 : R[T;T⁻¹])}).IsHopfIdeal R :=
  (isGroupLikeElem_T n).isHopfIdeal_span_sub_one

end CommRing

end LaurentPolynomial
