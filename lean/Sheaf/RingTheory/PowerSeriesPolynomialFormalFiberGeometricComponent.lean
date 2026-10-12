module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
Geometric-regularity component for the characteristic-p formal fibre theorem.
Source: Stacks Project, More on Algebra, Lemma 07PR.
(blueprint: new-lem-weil-pbc-helper-g-ring-char-p-geometric-component)
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- Regularity of the generic formal fibre after each finite purely inseparable base change.
Source: Stacks Project, More on Algebra, Lemma Tag 07PR, proof.
(blueprint: new-lem-weil-pbc-helper-g-ring-char-p-geometric-component)

Proof (the five steps of the node):
1. The power series ring is regular local (power-series-field-cohen-regular-complete).
   Polynomial extension is smooth (polynomial-ring-smooth), so A is regular by
   regular-ring-smooth-ascent. Prime localization and completion preserve regularity
   (regular-local-localization and completion-regular-local). The generic formal fibre
   is a localization of this completion, hence regular and Noetherian
   (adic-completion-noetherian). This is the degree-one base case.
2. Induct on the degree of a finite purely inseparable extension L/K. By
   finite-purely-inseparable-degree-p-intermediate choose K ⊆ M ⊆ L with L = M(z),
   z^p = f and [L:M] = p; f is not a p-th power in M. Apply induction to M.
3. By finite-subalgebra-fraction-field choose a finite A-subalgebra B of M with fraction
   field M. Write f = b/s and replace z by sz and f by s^p f = s^(p-1)b. The field L,
   degree p and failure to be a p-th power are unchanged, and now f belongs to B.
   Set C = B[z]/(z^p-f), finite free over B, a domain with fraction field L, since
   z has minimal polynomial of degree p. B is Noetherian (finite-algebra-noetherian).
   A is normal by regular-ring-normal and normal-domain-of-local-normal. By
   purely-inseparable-integral-prime-unique there is a unique prime r of B over q;
   radicial-prime-unique-degree-p gives a unique prime t of C over r. Since c^p is in B
   for every c in C, C tensor B_r is local and equals C_t. By completion-finite-quotient
   its completion is the polynomial quotient of the completion of B_r. Applying
   completion-finite-extension (07N9) to both B and C, and tensoring with their fraction
   fields, identifies the fibre over M with R = completion(B_r) tensor_B M and the fibre
   over L with R[z]/(z^p-f).
4. B is finite type over the complete Noetherian power series local ring. By
   derivation-nonzero-on-non-pth-power choose D:B → B with D(f) nonzero. Extend it to
   B_r, its completion and R by derivation-extends. The image of D(f) is a unit in R.
   By induction R is regular. Its polynomial ring is regular by polynomial-ring-smooth
   and regular-ring-smooth-ascent. Extend D coefficientwise, with D(z) = 0. It sends
   z^p-f to the unit -D(f), so hypersurface-derivation-regular gives regularity of
   R[z]/(z^p-f), and hence the fibre over L.
5. All finite purely inseparable base changes are regular. By def-weil-pbc-g-ring this
   proves geometric regularity; Noetherianity was obtained in step 1.

The base-change tensor product is the source's completion tensor_A L, by tensor
associativity and exchange of factors. This theorem supplies only the regularity
condition; Noetherianity of the original fibre is established independently. -/
theorem formalFiber_polynomial_geometricComponent
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime] :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    ∀ (k' : Type u) [Field k'] [Algebra ((⊥ : Ideal A).ResidueField) k']
      [Module.Finite ((⊥ : Ideal A).ResidueField) k']
      [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'],
      IsRegularRing (TensorProduct ((⊥ : Ideal A).ResidueField) k'
        ((⊥ : Ideal A).Fiber C)) := by
  sorry

end MvPowerSeries
