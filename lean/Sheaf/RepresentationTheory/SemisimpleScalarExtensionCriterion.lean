module

public import Sheaf.RepresentationTheory.FiniteModuleSplitGrothendieck
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-! # Integral representation classes detect split semisimple algebras

Source: ILO, Exposé X, Proposition 1.2, p.138, representation lifting before (5).
The criterion is an agent auxiliary algebra lemma, not an assertion of ILO.
(blueprint: lem-per-semisimple-scalar-extension-kzero-criterion)
-/

@[expose] public section

universe u v t z

namespace RepresentationTheory

/-- Surjectivity on integral split representation groups forces every division factor to be K.
Source: ILO X, Proposition 1.2, p.138, representation lifting before (5); agent auxiliary lemma.

Proof: use the given product decomposition and its central idempotents to decompose every
A-module into its factor modules. The matrix-division module classification identifies the
simple modules with column modules S_i and gives End_A(S_i) = D_i^op. The empty product has
no factors and the conclusion is vacuous. Every finite-dimensional module over B = Ω ⊗ A
is a quotient of B^n, hence semisimple. Socle complements and induction on dimension give a
finite decomposition into simples T_j. Scalar Schur identifies End_B(T_j) with Ω, so the
integer multiplicities dim_Ω Hom_B(T_j, -) detect the representation classes.
The central idempotents show that W_i = Ω ⊗ S_i is nonzero and that the W_i have disjoint
simple supports. Lift the class of one constituent T of W_i using integral surjectivity.
Writing the lift as a sum of integer multiples of [S_k], comparison of multiplicities gives
one integer times each multiplicity in W_i equal to the multiplicity in [T]. Thus that
integer and T's multiplicity are both one and every other multiplicity is zero: W_i is
simple. Finite-algebra Hom scalar extension identifies Ω ⊗ End_A(S_i) with End_B(W_i) = Ω.
Tensoring a K-basis therefore proves dim_K D_i = 1. Since 1 is nonzero it is a basis of D_i,
and the structural map K → D_i is bijective. The two auxiliary proof nodes for matrix
modules and Hom scalar extension have no Lean declaration yet; their imports remain for
stage 3. Scalar Schur and socle complements are the imported Mathlib declarations.
(blueprint: lem-per-semisimple-scalar-extension-kzero-criterion) -/
theorem divisionFactors_bijective_of_splitGrothendieck_surjective
    (K : Type u) [Field K] [CharZero K]
    (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : Type t) [Ring A] [Algebra K A] [Module.Finite K A]
    [IsSemisimpleRing A] [IsSemisimpleRing (TensorProduct K Ω A)]
    (hs : Function.Surjective
      (finiteModuleSplitScalarExtension.{u, v, max u v t, t} (K := K) (A := A) Ω))
    (r : ℕ) (d : Fin r → ℕ) (hd : ∀ i, 0 < d i)
    (D : Fin r → Type z) [∀ i, DivisionRing (D i)] [∀ i, Algebra K (D i)]
    [∀ i, Module.Finite K (D i)]
    (_e : A ≃ₐ[K] ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :
    ∀ i, Function.Bijective (algebraMap K (D i)) := by
  sorry

end RepresentationTheory
