module

public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.AlgebraicGeometry.ResidueField

import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Rational points of a finite field tensor over a receiving normal field

Source: Milne, Algebraic Groups (2017), Theorem B.37, Step 2, printed p.605;
Stacks Project, Tag 09HM, for normality.
(blueprint: lem-sfb-normal-field-tensor-rational-points)

The tensor has its usual commutative multiplication. All structural maps below
use `Algebra.TensorProduct.includeRight`, hence the scalar inclusion is
`a ↦ 1 ⊗ₜ a`, independently of the default left algebra structure on a tensor.
-/

@[expose] public section

universe u v w

open TensorProduct AlgebraicGeometry

namespace Algebra.TensorProduct

/-- Prime quotients and residue fields of `E ⊗[k] K` are canonically `K` when
`K/k` is a finite normal extension receiving the finite extension `E/k`.
The evaluation-kernel map bijects the `k`-embeddings `E → K` with the prime ideals.
No separability or reducedness is required.

Source: Milne, Algebraic Groups (2017), Theorem B.37, Step 2, printed p.605;
Stacks Project, Tags 09HM, 00J6, 00J7, 00KH, 00GK, 09GM, 01HV and 00CT.
(blueprint: lem-sfb-normal-field-tensor-rational-points)

Proof:
1. Expand first factors in a finite k-basis of E. The tensors of the basis
   elements with 1 span B over K, using the balancing relation of
   def-weil-pbc-module-tensor-product. Then lem-weil-pbc-finite-dim-algebra-artinian
   and lem-sfb-artinian-spectrum-finite give finiteness of the prime spectrum.
2. The tensor pushout universal property
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) constructs evaluation
   from an embedding σ and the identity of K, with value σ(e)a on e ⊗ a.
   It is onto K, so its kernel is prime. The given embedding supplies a prime.
3. For a prime q write D = B/q, j(a) = [1 ⊗ a], v(e) = [e ⊗ 1]. The quotient
   construction def-weil-pbc-algebra-hom-quotient makes D a nonzero domain and
   j injective. Finiteness makes e integral
   (lem-weil-pbc-finite-algebra-is-integral). Its minimal polynomial
   (the minimal-polynomial clause of def-weil-pbc-separable-algebraic-extension)
   equals that of u(e) and splits in K by normality. Evaluation in D gives a
   product of v(e) - j(a_i) equal to zero. Since D is a domain, v(e) = j(a_i)
   for some root, even when roots repeat.
4. Every tensor is a sum of pure tensors, so every element of D lies in j(K).
   Thus j is bijective. The embedding σ_q = j⁻¹ ∘ v has evaluation kernel q:
   the quotient map is j composed with evaluation, as checked on pure tensors.
5. Equal evaluation kernels force σ = τ, by applying evaluation at τ to
   e ⊗ 1 - 1 ⊗ σ(e). This proves the asserted bijection.
6. By lem-weil-pbc-affine-open-stalk-localization the stalk at q is B_q with
   its actual germ map. By lem-weil-pbc-prime-residue-field-algebra its residue
   field is the fraction field of D. Since D is already the field K through j,
   its fraction-field map is an isomorphism, as is the composite from K.
   The displayed global evaluation uses precisely that structural germ map. -/
theorem normal_tensor_rational_points
    {k : Type u} {E : Type v} {K : Type w}
    [Field k] [Field E] [Field K] [Algebra k E] [Algebra k K]
    [FiniteDimensional k E] [FiniteDimensional k K] [Normal k K]
    (_u : E →ₐ[k] K) :
    {q : Ideal (E ⊗[k] K) | q.IsPrime}.Finite ∧
      {q : Ideal (E ⊗[k] K) | q.IsPrime}.Nonempty ∧
      (∀ (q : Ideal (E ⊗[k] K)), q.IsPrime →
        Function.Bijective
          ((Ideal.Quotient.mk q).comp
            (includeRight : K →ₐ[k] E ⊗[k] K).toRingHom)) ∧
      Set.BijOn
        (fun σ : E →ₐ[k] K ↦ RingHom.ker (productMap σ (AlgHom.id k K)).toRingHom)
        Set.univ {q : Ideal (E ⊗[k] K) | q.IsPrime} ∧
      (∀ x : Spec (CommRingCat.of (E ⊗[k] K)),
        Function.Bijective
          (((Spec (CommRingCat.of (E ⊗[k] K))).Γevaluation x).hom.comp
            (((Scheme.ΓSpecIso (CommRingCat.of (E ⊗[k] K))).inv).hom.comp
              (includeRight : K →ₐ[k] E ⊗[k] K).toRingHom))) := by
  sorry

end Algebra.TensorProduct
