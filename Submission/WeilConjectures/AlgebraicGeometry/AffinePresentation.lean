/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RingHom.StandardSmooth

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Affine presentations of schemes of finite type over a field

We collect elementary scheme-theoretic and commutative-algebra facts about affine schemes of
finite type over a field `k₀`:

* every affine `k₀`-scheme of finite type is isomorphic over `Spec k₀` to the spectrum of a
  quotient of a polynomial ring `k₀[X₀, …, X_{n-1}]`;
* the projection `Spec (k₀[X₀, …, Xₙ] ⧸ I) ⟶ 𝔸ⁿ` forgetting the last coordinate, and the
  description of its fibres over `k₀`-points as spectra of quotients of `k₀[X]`;
* finiteness of `Spec (k₀[X] ⧸ J)` for `J ≠ ⊥` and smoothness of `𝔸¹`;
* descent of Frobenius-fixed points of affine schemes over a finite field.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

section SpecIso

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

end SpecIso

section Presentation

variable {k₀ : Type u} [Field k₀]


end Presentation

section BaseCases

variable {k₀ : Type u} [Field k₀]


/-- The polynomial algebra `R[X₀, …, X_{n-1}]` is standard smooth of relative dimension `n`
over `R`. -/
lemma isStandardSmoothOfRelativeDimension_mvPolynomial (R : Type u) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  let v : PEmpty.{1} → MvPolynomial (Fin n) R := PEmpty.elim
  let P : Algebra.PreSubmersivePresentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) (Fin n) PEmpty.{1} :=
    .naive PEmpty.elim (fun a ↦ a.elim)
  let Q : Algebra.SubmersivePresentation R _ (Fin n) PEmpty.{1} :=
    { P with jacobian_isUnit := by simp [P.jacobian_eq_jacobiMatrix_det] }
  let e : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) ≃ₐ[R] MvPolynomial (Fin n) R :=
    (Ideal.quotientEquivAlgOfEq R (by simp [v])).trans (AlgEquiv.quotientBot R _)
  exact (Q.ofAlgEquiv e).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])


end BaseCases

section Projection

variable {k₀ : Type u} [Field k₀] {n : ℕ}

/-- The ring map `k₀[X₀, …, X_{n-1}] →+* k₀[X₀, …, Xₙ] ⧸ I` induced by the inclusion of the
first `n` variables. -/
noncomputable def mvPolynomialQuotientProjectionRingHom
    (I : Ideal (MvPolynomial (Fin (n + 1)) k₀)) :
    MvPolynomial (Fin n) k₀ →+* MvPolynomial (Fin (n + 1)) k₀ ⧸ I :=
  (Ideal.Quotient.mk I).comp (rename Fin.castSucc).toRingHom

/-- Evaluation of the first `n` variables of `k₀[X₀, …, Xₙ]` at `a`, sending the last variable
to the variable of `k₀[X]`. -/
noncomputable def evalInitAlgHom (a : Fin n → k₀) :
    MvPolynomial (Fin (n + 1)) k₀ →ₐ[k₀] MvPolynomial (Fin 1) k₀ :=
  aeval (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin 1) k₀) (fun i ↦ C (a i)) (X 0))

/-- `evalInitAlgHom a` sends the `i`-th of the first `n` variables to `a i`. -/
@[simp]
lemma evalInitAlgHom_X_castSucc (a : Fin n → k₀) (i : Fin n) :
    evalInitAlgHom a (X i.castSucc) = C (a i) := by
  simp [evalInitAlgHom]

/-- `evalInitAlgHom a` sends the last variable to the variable of `k₀[X]`. -/
@[simp]
lemma evalInitAlgHom_X_last (a : Fin n → k₀) : evalInitAlgHom a (X (Fin.last n)) = X 0 := by
  simp [evalInitAlgHom]

/-- The ideal of `k₀[X]` obtained from `I` by evaluating the first `n` variables at `a`. -/
noncomputable def evalInitIdeal (a : Fin n → k₀) (I : Ideal (MvPolynomial (Fin (n + 1)) k₀)) :
    Ideal (MvPolynomial (Fin 1) k₀) :=
  I.map (evalInitAlgHom a).toRingHom

/-- The ring map `k₀[X₀, …, Xₙ] ⧸ I →+* k₀[X] ⧸ evalInitIdeal a I` induced by
`evalInitAlgHom a`. -/
noncomputable def evalInitQuotientRingHom (a : Fin n → k₀)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k₀)) :
    MvPolynomial (Fin (n + 1)) k₀ ⧸ I →+* MvPolynomial (Fin 1) k₀ ⧸ evalInitIdeal a I :=
  Ideal.quotientMap _ (evalInitAlgHom a).toRingHom Ideal.le_comap_map

/-- `evalInitQuotientRingHom` on residue classes of polynomials. -/
@[simp]
lemma evalInitQuotientRingHom_mk (a : Fin n → k₀) (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (p : MvPolynomial (Fin (n + 1)) k₀) :
    evalInitQuotientRingHom a I (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk _ (evalInitAlgHom a p) :=
  rfl

variable {T : Type*} [CommRing T]

/-- Given a commutative square out of `k₀[X₀, …, X_{n-1}]`, the composite of evaluation with
the induced map on `k₀[X]` agrees with the given map on `k₀[X₀, …, Xₙ]`. -/
lemma eval₂Hom_comp_evalInitAlgHom (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (φ : MvPolynomial (Fin n) k₀ →ₐ[k₀] k₀) (α : MvPolynomial (Fin (n + 1)) k₀ ⧸ I →+* T)
    (β : k₀ →+* T) (h : α.comp (mvPolynomialQuotientProjectionRingHom I) = β.comp φ.toRingHom) :
    (eval₂Hom β fun _ ↦ α (Ideal.Quotient.mk I (X (Fin.last n)))).comp
        (evalInitAlgHom fun i ↦ φ (X i)).toRingHom =
      α.comp (Ideal.Quotient.mk I) := by
  have h' (p : MvPolynomial (Fin n) k₀) :
      α (Ideal.Quotient.mk I (rename Fin.castSucc p)) = β (φ p) := congr($h p)
  refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
  · simpa using (h' (C c)).symm
  · induction i using Fin.lastCases with
    | last => simp
    | cast j => simpa using (h' (X j)).symm

/-- The map out of `k₀[X] ⧸ evalInitIdeal a I` induced by a commutative square out of
`k₀[X₀, …, X_{n-1}]`. -/
noncomputable def evalInitDesc (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (φ : MvPolynomial (Fin n) k₀ →ₐ[k₀] k₀) (α : MvPolynomial (Fin (n + 1)) k₀ ⧸ I →+* T)
    (β : k₀ →+* T) (h : α.comp (mvPolynomialQuotientProjectionRingHom I) = β.comp φ.toRingHom) :
    MvPolynomial (Fin 1) k₀ ⧸ evalInitIdeal (fun i ↦ φ (X i)) I →+* T :=
  Ideal.Quotient.lift _ (eval₂Hom β fun _ ↦ α (Ideal.Quotient.mk I (X (Fin.last n)))) <| by
    have hle : evalInitIdeal (fun i ↦ φ (X i)) I ≤
        RingHom.ker (eval₂Hom β fun _ ↦ α (Ideal.Quotient.mk I (X (Fin.last n)))) := by
      refine Ideal.map_le_iff_le_comap.mpr fun p hp ↦ ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
        eval₂Hom_comp_evalInitAlgHom I φ α β h, RingHom.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    exact fun x hx ↦ hle hx

/-- `evalInitDesc` on residue classes of polynomials. -/
@[simp]
lemma evalInitDesc_mk (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (φ : MvPolynomial (Fin n) k₀ →ₐ[k₀] k₀) (α : MvPolynomial (Fin (n + 1)) k₀ ⧸ I →+* T)
    (β : k₀ →+* T) (h : α.comp (mvPolynomialQuotientProjectionRingHom I) = β.comp φ.toRingHom)
    (p : MvPolynomial (Fin 1) k₀) :
    evalInitDesc I φ α β h (Ideal.Quotient.mk _ p) =
      eval₂Hom β (fun _ ↦ α (Ideal.Quotient.mk I (X (Fin.last n)))) p :=
  rfl


end Projection

section Frobenius


end Frobenius

end AlgebraicGeometry
