/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic

/-! # Lifting a normalized tensor factor through a finite DVR extension

Source: Stacks Project, Tags 09EM and 032L, and lying over.
(blueprint: lem-sbc-dvr-normalized-tensor-factor-lift) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- A closed prime of a normalized tensor factor lifts after finite DVR base change.

Source: Stacks Project, Tag 09EM (remark-setup), Tag 032L and lying over.
(blueprint: lem-sbc-dvr-normalized-tensor-factor-lift)

Proof: Invert B minus zero to regard F as a finite separable field factor of
E tensor Frac(A) over Frac(B). The finite faithful extension A₁/A embeds
Frac(A) in Frac(A₁). Take the finite product of fields obtained by tensoring
F with Frac(A₁) over Frac(A). Its factors are also factors of
E tensor Frac(A₁) over Frac(B), hence quotients by maximal ideals P₁ of
E tensor A₁ over B. Their right maps alpha₁ are injective. Normalize S in
this product. Since E/Frac(B) is separable the factors are finite separable
over Frac(A₁), and 032L makes their normalizations S₁ finite over A₁.
Integrality over A, A₁ and S agrees, by transitivity and normality, so these
are exactly the factors of that product normalization. The integral map
S -> product S₁ is injective. Lying over lifts Q to a prime in one factor,
giving Q₁ and the induced A-algebra map i. Its contraction to A₁ lies over
the maximal ideal of A. Since A₁/A is finite and A₁ is local, this
contraction is the maximal ideal of A₁. The ring S is a finite normal
one-dimensional domain, hence Dedekind. The inclusion into the chosen
factor is injective, so S₁ is torsion free over S and therefore flat.
This construction uses no tameness or ramification bound. -/
theorem dvr_normalized_tensor_factor_lift
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A]
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ Algebra.IsSeparable (FractionRing B) E) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    ∀ (P : Ideal (E ⊗[B] A)) (hP : P.IsMaximal),
    letI := hP
    let F := (E ⊗[B] A) ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).toRingHom
    letI := alpha.toAlgebra
    Function.Injective alpha →
    let S := integralClosure A F
    Module.Finite A S →
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    Q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A →
    ∀ (A₁ : Type u) [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
      [Algebra A A₁] [Algebra B A₁] [IsScalarTower B A A₁]
      [Module.Finite A A₁] [FaithfulSMul A A₁],
    ∃ (P₁ : Ideal (E ⊗[B] A₁)) (hP₁ : P₁.IsMaximal),
    letI := hP₁
    let F₁ := (E ⊗[B] A₁) ⧸ P₁
    let alpha₁ : A₁ →+* F₁ := (Ideal.Quotient.mk P₁).comp
      (Algebra.TensorProduct.includeRight : A₁ →ₐ[B] E ⊗[B] A₁).toRingHom
    letI := alpha₁.toAlgebra
    letI : Algebra A F₁ := (alpha₁.comp (algebraMap A A₁)).toAlgebra
    letI : IsScalarTower A A₁ F₁ := .of_algebraMap_eq' rfl
    let S₁ := integralClosure A₁ F₁
    Function.Injective alpha₁ ∧ Module.Finite A₁ S₁ ∧
    ∃ (i : S →ₐ[A] S₁) (Q₁ : Ideal S₁),
      Q₁.IsPrime ∧ Q₁.comap i.toRingHom = Q ∧
      Q₁.comap (algebraMap A₁ S₁) = IsLocalRing.maximalIdeal A₁ ∧
      letI := i.toRingHom.toAlgebra
      Module.Flat S S₁ := by sorry

end RingTheory
