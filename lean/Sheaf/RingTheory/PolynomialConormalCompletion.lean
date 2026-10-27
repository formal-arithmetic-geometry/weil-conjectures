module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Topology.Order
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Completion of a polynomial presentation and its conormal differential

Source: Stacks Project, restricted.tex, Tag 0GAF (lemma-NL-is-completion),
and equation-NL (blueprint: lem-per-polynomial-conormal-completion).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace Algebra

/-- Completing a finite polynomial presentation preserves the conormal differential.
The cotangents of `Extension.ofSurjective` are the actual kernel modulo its square,
with the quotient-ring scalar action. All maps below are fixed by their formulas.
The topology displayed in `Continuous` is the initial topology of the discrete residue
projections, namely the inverse-limit topology. Finite products represent the finite
free modules, including the zero free module when `r = 0`.

Source: Stacks Project, restricted.tex, Tag 0GAF (lemma-NL-is-completion) and
 equation-NL (blueprint: lem-per-polynomial-conormal-completion).

Proof:
1. By lem-weil-pbc-finite-type-algebra-noetherian the polynomial ring is Noetherian.
   Its kernel, kernel square, quotient and conormal are finite modules. Completion at
   the extended base ideal is the stated base-ideal completion.
2. Apply lem-weil-pbc-completion-exact-finite-modules to the presentation. The natural
   comparison of lem-weil-pbc-completion-finite-module-tensor identifies the completed
   kernel with its extended ideal. This proves surjectivity and the kernel equality.
3. Complete the sequence from the kernel square to the kernel to its conormal.
   The image of the completed square is the extended square, which equals the square
   of the extended kernel by expanding products of generators.
4. The same tensor-completion comparison and tensor balancing identify this quotient
   with the conormal tensored over B with its completion. A lift of a completed scalar
   gives the formula below; changing the lift changes the tensor by a kernel multiple,
   which annihilates the conormal.
5. Each polynomial partial derivative preserves every power of the extended base
   ideal by A-linearity. Descend to every residue ring and apply coordinatewise.
   Compatibility and the Leibniz rule hold coordinatewise; preservation of projection
   kernels proves continuity for the inverse-limit topology.
6. The Leibniz rule kills the kernel square after projection to B, respectively its
   completion. It also gives B-linearity and completed-B-linearity, so both displayed
   differential formulas descend to the conormal quotients.
7. The free-module tensor identification sends v tensor b to (b v_i)_i, with inverse
   the finite sum of basis vectors tensored with coordinates. On a conormal generator
   multiplied by a lift p, the product rule kills the term containing the kernel
   element and leaves alphaHat(p) times its algebraic derivative. Pure tensors span,
   proving the final equality. The empty finite sum covers r = 0.
-/
theorem polynomial_conormal_completion
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] (I : Ideal A) (r : ℕ)
    (α : MvPolynomial (Fin r) A →ₐ[A] B) (hα : Function.Surjective α)
    (hK : (RingHom.ker α.toRingHom).FG) :
    ∃ αHat :
        AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
          (MvPolynomial (Fin r) A) →ₐ[A]
        AdicCompletion (I.map (algebraMap A B)) B,
      (∀ (n : ℕ)
        (x : AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
          (MvPolynomial (Fin r) A)) (f : MvPolynomial (Fin r) A),
        AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial (Fin r) A))) n x =
          Ideal.Quotient.mk _ f →
        AdicCompletion.evalₐ (I.map (algebraMap A B)) n (αHat x) =
          Ideal.Quotient.mk _ (α f)) ∧
      ∃ hαHat : Function.Surjective αHat,
        RingHom.ker αHat.toRingHom =
          (RingHom.ker α.toRingHom).map
            (algebraMap (MvPolynomial (Fin r) A)
              (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
                (MvPolynomial (Fin r) A))) ∧
        ∃ D : Fin r → Derivation A
            (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
              (MvPolynomial (Fin r) A))
            (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
              (MvPolynomial (Fin r) A)),
          (∀ (i : Fin r) (n : ℕ)
            (x : AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
              (MvPolynomial (Fin r) A)) (f : MvPolynomial (Fin r) A),
            AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial (Fin r) A))) n x =
              Ideal.Quotient.mk _ f →
            AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial (Fin r) A))) n
                (D i x) = Ideal.Quotient.mk _ (MvPolynomial.pderiv i f)) ∧
          (∀ i : Fin r, @Continuous _ _
            (⨅ n : ℕ, TopologicalSpace.induced
              (AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial (Fin r) A))) n) ⊥)
            (⨅ n : ℕ, TopologicalSpace.induced
              (AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial (Fin r) A))) n) ⊥)
            (D i)) ∧
          ∃ e :
              TensorProduct B (Extension.ofSurjective α hα).Cotangent
                (AdicCompletion (I.map (algebraMap A B)) B) ≃ₗ[B]
              (Extension.ofSurjective αHat hαHat).Cotangent,
            (∀ (f : (Extension.ofSurjective α hα).ker)
              (p : AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
                (MvPolynomial (Fin r) A))
              (g : (Extension.ofSurjective αHat hαHat).ker),
              g.val = p * algebraMap (MvPolynomial (Fin r) A)
                (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
                  (MvPolynomial (Fin r) A)) f.val →
              e (TensorProduct.tmul B (Extension.Cotangent.mk f) (αHat p)) =
                Extension.Cotangent.mk g) ∧
            (∀ (b : AdicCompletion (I.map (algebraMap A B)) B)
              (z : TensorProduct B (Extension.ofSurjective α hα).Cotangent
                (AdicCompletion (I.map (algebraMap A B)) B)),
              e (LinearMap.lTensor _ (b • (LinearMap.id :
                AdicCompletion (I.map (algebraMap A B)) B →ₗ[B]
                AdicCompletion (I.map (algebraMap A B)) B)) z) = b • e z) ∧
            ∃ d₀ : (Extension.ofSurjective α hα).Cotangent →ₗ[B] (Fin r → B),
              ∃ dHat : (Extension.ofSurjective αHat hαHat).Cotangent →ₗ[
                  AdicCompletion (I.map (algebraMap A B)) B]
                  (Fin r → AdicCompletion (I.map (algebraMap A B)) B),
                (∀ (f : (Extension.ofSurjective α hα).ker) (i : Fin r),
                  d₀ (Extension.Cotangent.mk f) i = α (MvPolynomial.pderiv i f.val)) ∧
                (∀ (g : (Extension.ofSurjective αHat hαHat).ker) (i : Fin r),
                  dHat (Extension.Cotangent.mk g) i = αHat (D i g.val)) ∧
                ∃ eFree :
                    TensorProduct B (Fin r → B)
                      (AdicCompletion (I.map (algebraMap A B)) B) ≃ₗ[B]
                    (Fin r → AdicCompletion (I.map (algebraMap A B)) B),
                  (∀ (w : Fin r → B) (b : AdicCompletion (I.map (algebraMap A B)) B)
                    (i : Fin r),
                    eFree (TensorProduct.tmul B w b) i =
                      b * algebraMap B _ (w i)) ∧
                  (∀ (b : AdicCompletion (I.map (algebraMap A B)) B)
                    (z : TensorProduct B (Fin r → B)
                      (AdicCompletion (I.map (algebraMap A B)) B)),
                    eFree (LinearMap.lTensor _ (b • (LinearMap.id :
                      AdicCompletion (I.map (algebraMap A B)) B →ₗ[B]
                      AdicCompletion (I.map (algebraMap A B)) B)) z) = b • eFree z) ∧
                  ∀ z : TensorProduct B (Extension.ofSurjective α hα).Cotangent
                    (AdicCompletion (I.map (algebraMap A B)) B),
                    dHat (e z) = eFree ((LinearMap.rTensor
                      (AdicCompletion (I.map (algebraMap A B)) B) d₀) z) := by
  sorry

end Algebra
