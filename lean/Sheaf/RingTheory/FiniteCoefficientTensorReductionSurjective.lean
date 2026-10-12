/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Surjectivity of a finite coefficient tensor map modulo the model maximal ideal

Source: Stacks Project, Remark 07NS (parts (1), (3)), finite nilpotent reduction.
(blueprint: lem-weil-pbc-finite-coefficient-tensor-reduction-surjective)
-/

@[expose] public section

universe u v w z

namespace RingHom

/-- Surjectivity on the closed fibre implies surjectivity modulo m_C B.
Source: Stacks Project, Remark 07NS (parts (1), (3)), the nilpotent Nakayama argument.
(blueprint: lem-weil-pbc-finite-coefficient-tensor-reduction-surjective)

Proof:
1. Finiteness makes A/m₀A a finite-dimensional k₀-algebra, hence Artinian local.
   Nilpotence of its maximal ideal gives m_A^N ⊆ m₀A for some positive N.
2. Surjectivity of C → B/m_A B says B = ψ(C) + m_A B. The image of F is a
   subring containing ψ(C) and φ(A), since F(c ⊗ 1) = ψ(c) and F(1 ⊗ a) = φ(a).
   For b in m_A^i B expand b as a finite sum φ(x_j)b_j. Decompose each b_j as
   ψ(c_j) plus an element of m_A B; the first terms belong to F(D), the second
   to m_A^(i+1) B. Induction gives B = F(D) + m_A^N B.
3. Compatibility ψγ = φα sends m₀B into m_C B because γ is local. Hence
   m_A^N B ⊆ m₀B ⊆ m_C B. Every class in B/m_C B is therefore the image of
   some tensor under F. Neither completeness nor flatness is used.
-/
theorem finite_coefficient_tensor_reduction_surjective
    {A₀ : Type u} {A : Type v} {B : Type w} {C : Type z}
    [CommRing A₀] [CommRing A] [CommRing B] [CommRing C]
    [Algebra A₀ A] [Algebra A₀ C]
    [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (α : A₀ →+* A) (hα : algebraMap A₀ A = α) [IsLocalHom α]
    [Module.Finite A₀ A]
    (γ : A₀ →+* C) (hγ : algebraMap A₀ C = γ) [IsLocalHom γ]
    (φ : A →+* B) [IsLocalHom φ]
    (ψ : C →+* B) [IsLocalHom ψ] (hψγ : ψ.comp γ = φ.comp α)
    (F : TensorProduct A₀ C A →+* B)
    (hF : ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a)
    (hres : Function.Surjective
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ)).comp ψ)) :
    Function.Surjective
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal C).map ψ)).comp F) := by sorry

end RingHom
