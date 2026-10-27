/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Polynomial presentations and conormal modules after extending a field

Source: Stacks Project, Algebra, Tags 00S4 and 00SJ, proofs of
lemma-change-base-NL and lemma-lci-field-change
(blueprint: lem-weil-pbc-polynomial-conormal-field-comparison).

Tensor products of rings keep the order `S ⊗[k] K`. Scalar extension of modules
is written with the scalar ring first, using the canonical tensor commutor.
The normalized formulas express the right-factor `K`-algebra structures without
installing a second algebra instance on the ring tensor product.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open TensorProduct

namespace MvPolynomial

/-- Extending a field preserves a polynomial presentation, its ideal, its square,
and its conormal module, with all the canonical maps and their compatibility.
The ideal comparisons displayed as `k`-linear equivalences are `K`-linear by
their pure-tensor formulas; the quotient map is explicitly a `K`-algebra equivalence.
The conormal modules use `Algebra.Extension.Cotangent`, whose action is precisely
multiplication by a lift along the presentation. The final equivalence is linear
over the actual quotient algebra `S ⊗[k] K`.

Source: Stacks Project, Algebra, Tags 00S4 and 00SJ
(blueprint: lem-weil-pbc-polynomial-conormal-field-comparison).

Proof:
1. Define mu on pure tensors by coefficient extension and scalar multiplication.
Its inverse sends a polynomial sum of lambda_a x^a to the sum of x^a tensor
lambda_a. Polynomial and tensor universal properties give multiplicativity;
balancing on coefficients gives both inverse identities.
2. Every vector space is flat (lem-weil-pbc-module-over-field-flat). Tensoring
J into P is injective by lem-weil-pbc-flat-tensor-exact. Its image under mu is
the K-span of rho(J), an ideal because multiplication by monomials preserves J.
It is exactly the extended ideal. Apply this to I and I squared. Products of
generators show that extension commutes with squares. Both maps restrict mu,
so the inclusion squares commute.
3. Evaluate the variables at alpha(x_i) tensor 1 to define alphaK. Its composite
with rho agrees with j alpha on coefficients and variables. Tensor exactness
gives surjectivity and kernel IK. The induced quotient map is therefore an
algebra equivalence, normalized on every polynomial. This finite-variable
presentation shows finite type.
4. The polynomial ring is Noetherian by
lem-weil-pbc-polynomial-ring-field-regular-ring. Its ideal I is finite by
lem-weil-pbc-noetherian-submodule-finite. Classes of its generators generate
I/I squared over S; multiplication by a lift defines the S-action independently
of the lift, since differences multiply I into I squared.
5. Tensor I squared into I onto I/I squared with K. Exactness identifies the
quotient with IK/IK squared by the compatible ideal and square equivalences.
This gives e, normalized on each relation tensor lambda, including the
commuting quotient square for arbitrary ideal tensors.
6. Tensor balancing gives gamma, sending (s tensor lambda) tensor m to
(s m) tensor lambda; its inverse sends m tensor lambda to
(1 tensor lambda) tensor m. These are inverse also for the zero module.
7. Set theta = e gamma. Lifting s to p gives the specified formula
[lambda rho(p f)]. Changing a lift or representative changes the result by
IK squared. Lifting the first scalar factor also proves S_K-linearity on
pure tensors and hence everywhere. The quotient square from step 5 proves
that the final map is the quotient of the compatible ideal comparisons. -/
theorem polynomial_conormal_field_comparison
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (S : Type w) [CommRing S] [Algebra k S] (n : ℕ)
    (α : MvPolynomial (Fin n) k →ₐ[k] S) (hα : Function.Surjective α) :
    ∃ μ : @AlgEquiv K (MvPolynomial (Fin n) k ⊗[k] K) (MvPolynomial (Fin n) K)
      _ _ _ Algebra.TensorProduct.rightAlgebra inferInstance,
    ∃ αK : MvPolynomial (Fin n) K →ₐ[k] (S ⊗[k] K),
    ∃ hαK : Function.Surjective αK,
    ∃ IK : Ideal (MvPolynomial (Fin n) K),
      IK = (RingHom.ker α.toRingHom).map (MvPolynomial.map (algebraMap k K)) ∧
      RingHom.ker αK.toRingHom = IK ∧
      (∀ (p : MvPolynomial (Fin n) k) (l : K),
        μ (p ⊗ₜ[k] l) = l • MvPolynomial.map (algebraMap k K) p) ∧
      (∀ i : Fin n, αK (MvPolynomial.X i) = α (MvPolynomial.X i) ⊗ₜ[k] (1 : K)) ∧
      (∀ l : K, αK (MvPolynomial.C l) = (1 : S) ⊗ₜ[k] l) ∧
      (∀ p : MvPolynomial (Fin n) k,
        αK (MvPolynomial.map (algebraMap k K) p) = α p ⊗ₜ[k] (1 : K)) ∧
      (∃ q : @AlgEquiv K (MvPolynomial (Fin n) K ⧸ IK) (S ⊗[k] K)
          _ _ _ inferInstance Algebra.TensorProduct.rightAlgebra,
        ∀ p : MvPolynomial (Fin n) K, q (Ideal.Quotient.mk IK p) = αK p) ∧
      RingHom.FiniteType
        (Algebra.TensorProduct.includeRight.toRingHom : K →+* S ⊗[k] K) ∧
      Module.Finite S (Algebra.Extension.ofSurjective α hα).Cotangent ∧
      ∃ eI : ((RingHom.ker α.toRingHom) ⊗[k] K) ≃ₗ[k] IK,
      ∃ eSq : ((RingHom.ker α.toRingHom ^ 2 : Ideal _) ⊗[k] K) ≃ₗ[k] (IK ^ 2 : Ideal _),
      ∃ e : ((Algebra.Extension.ofSurjective α hα).Cotangent ⊗[k] K) ≃ₗ[k]
        (Algebra.Extension.ofSurjective αK hαK).Cotangent,
      ∃ γ : ((S ⊗[k] K) ⊗[S] (Algebra.Extension.ofSurjective α hα).Cotangent) ≃ₗ[k]
        ((Algebra.Extension.ofSurjective α hα).Cotangent ⊗[k] K),
      ∃ Θ : ((S ⊗[k] K) ⊗[S] (Algebra.Extension.ofSurjective α hα).Cotangent)
          ≃ₗ[S ⊗[k] K] (Algebra.Extension.ofSurjective αK hαK).Cotangent,
        (∀ z : (RingHom.ker α.toRingHom) ⊗[k] K, (eI z : MvPolynomial (Fin n) K) =
          μ (LinearMap.rTensor K ((RingHom.ker α.toRingHom).subtype.restrictScalars k) z)) ∧
        (∀ z : (RingHom.ker α.toRingHom ^ 2 : Ideal _) ⊗[k] K, (eSq z : MvPolynomial (Fin n) K) =
          μ (LinearMap.rTensor K
            ((RingHom.ker α.toRingHom ^ 2).subtype.restrictScalars k) z)) ∧
        (∀ z : (RingHom.ker α.toRingHom ^ 2 : Ideal _) ⊗[k] K, (eSq z : MvPolynomial (Fin n) K) =
          (eI (LinearMap.rTensor K
            ((Submodule.inclusion (Ideal.pow_le_self (I := RingHom.ker α.toRingHom)
              two_ne_zero)).restrictScalars k) z) : MvPolynomial (Fin n) K)) ∧
        (∀ (s : S) (l : K) (m : (Algebra.Extension.ofSurjective α hα).Cotangent),
          γ ((s ⊗ₜ[k] l) ⊗ₜ[S] m) = (s • m) ⊗ₜ[k] l) ∧
        (∀ z : (S ⊗[k] K) ⊗[S] (Algebra.Extension.ofSurjective α hα).Cotangent,
          Θ z = e (γ z)) ∧
        (∀ (z : (RingHom.ker α.toRingHom) ⊗[k] K)
            (g : (Algebra.Extension.ofSurjective αK hαK).ker),
          (g.val : MvPolynomial (Fin n) K) = (eI z : MvPolynomial (Fin n) K) →
          e (LinearMap.rTensor K
            ((Algebra.Extension.Cotangent.mk
              (P := Algebra.Extension.ofSurjective α hα)).restrictScalars k) z) =
            Algebra.Extension.Cotangent.mk g) ∧
        (∀ (f : (Algebra.Extension.ofSurjective α hα).ker)
            (s : S) (l : K) (p : MvPolynomial (Fin n) k)
            (g : (Algebra.Extension.ofSurjective αK hαK).ker),
          α p = s →
          (g.val : MvPolynomial (Fin n) K) =
            l • MvPolynomial.map (algebraMap k K) (p * @id (MvPolynomial (Fin n) k) f.val) →
          Θ ((s ⊗ₜ[k] l) ⊗ₜ[S] Algebra.Extension.Cotangent.mk f) =
            Algebra.Extension.Cotangent.mk g) := by
  sorry

end MvPolynomial
