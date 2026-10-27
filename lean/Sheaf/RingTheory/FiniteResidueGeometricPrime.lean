module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Geometric prime quotients above a finite residue field

Source: Stacks Project, Algebra, Tags 00FV, 00CX, 00GS, 00CO and 07BH;
Fields, Tag 09GR (blueprint: lem-trf-finite-residue-geometric-prime).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- A prime above a maximal ideal with finite residue quotient has scalar quotient and
residue field after extension to an algebraically closed field. The existential map is
specified on every pure tensor, so it is the canonical map, not a choice of an unrelated
surjection. The applied lambda supplies Mathlib's right-factor algebra structures.
Bijectivity of the structural algebra maps expresses that they are algebra isomorphisms.

Source: Stacks Project, Algebra, Tags 00FV, 00CX, 00GS, 00CO and 07BH;
Fields, Tag 09GR (blueprint: lem-trf-finite-residue-geometric-prime).

Proof:
1. Write B = (T tensor Omega)/q and pi for its quotient map. Contraction q = p shows
   that pi(t tensor lambda) is unchanged on replacing t by t + a with a in p:
   pi(a tensor lambda) = pi((a tensor 1)(1 tensor lambda)) = 0. This gives a
   well-defined k-bilinear map (T/p) times Omega to B. The tensor universal property
   gives h with the displayed formula. Multiplication on pure tensors and their finite
   sums proves multiplicativity; h(1 tensor 1) = 1 and h(1 tensor lambda) is the
   structural image of lambda. Thus h is an Omega-algebra homomorphism. Lifting a
   finite sum of pure tensors from B proves surjectivity
   (def-weil-pbc-algebra-hom-quotient, def-weil-pbc-module-tensor-product).
2. A finite k-spanning family e_j of T/p gives the Omega-spanning family e_j tensor 1
   of its tensor product: x tensor lambda = sum_j e_j tensor (c_j lambda) when
   x = sum_j c_j e_j. Its image under h spans B, proving finite dimensionality
   (def-weil-finite-dimensional-subspace, def-weil-pbc-module-tensor-product).
3. Since q is prime, B is a nonzero domain. The finite-dimensional domain lemma
   (lem-weil-pbc-finite-dimensional-domain-is-field, Tag 00GS) makes B a field.
   Consequently q is maximal.
4. The algebraically closed finite-extension lemma
   (lem-weil-pbc-alg-closed-finite-extension-trivial, Tag 09GR) says that the actual
   structural map Omega to B is bijective, hence an Omega-algebra isomorphism.
5. For s outside q, pi(s) is nonzero. The map T_tensor_Omega localized at q to B
   sending x/s to pi(x)/pi(s) respects fraction equality: cancel the nonzero image
   of the common multiplier outside q. It preserves addition and multiplication,
   is surjective via x/1, and has kernel q extended to the localization. It induces
   the canonical isomorphism kappa(q) to B, inverse to pi(x) mapping to [x/1]
   (def-weil-pbc-localization-at-prime, Tags 00CO and 07BH). This isomorphism carries
   the structural image of each lambda to pi(1 tensor lambda). Therefore the
   structural map Omega to kappa(q) is bijective as well. -/
theorem finite_residue_geometric_prime
    (k : Type u) (Ω : Type v) (T : Type w)
    [Field k] [Field Ω] [IsAlgClosed Ω] [CommRing T] [Algebra k Ω] [Algebra k T]
    (p : Ideal T) [p.IsMaximal] [FiniteDimensional k (T ⧸ p)]
    (q : Ideal (T ⊗[k] Ω)) [q.IsPrime]
    (hq : q.comap (includeLeft : T →ₐ[k] T ⊗[k] Ω).toRingHom = p) :
    (fun (_instS : Algebra Ω (T ⊗[k] Ω))
      (_instF : Algebra Ω ((T ⧸ p) ⊗[k] Ω)) ↦
      (∃ h : ((T ⧸ p) ⊗[k] Ω) →ₐ[Ω] ((T ⊗[k] Ω) ⧸ q),
        (∀ (t : T) (a : Ω),
          h (Ideal.Quotient.mk p t ⊗ₜ[k] a) = Ideal.Quotient.mk q (t ⊗ₜ[k] a)) ∧
        Function.Surjective h) ∧
      FiniteDimensional Ω ((T ⊗[k] Ω) ⧸ q) ∧
      q.IsMaximal ∧
      Function.Bijective (algebraMap Ω ((T ⊗[k] Ω) ⧸ q)) ∧
      Function.Bijective (algebraMap Ω q.ResidueField))
      (rightAlgebra (R := k) (A := T) (B := Ω))
      (rightAlgebra (R := k) (A := T ⧸ p) (B := Ω)) := by
  sorry

end Algebra.TensorProduct
