module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Specialization of a generic polynomial relation over a valuation ring

Source: Stacks Project, Algebra, Tag 00QK,
`lemma-finite-type-domain-over-valuation-ring-dim-fibres`, the generic polynomial kernel,
normalization by a coefficient of minimal valuation, and reduction to the residue field
(blueprint: lem-trf-valuation-generic-relation-specialization).

The coefficient action of `K` on `FractionRing (B ⊗[A] K)` is written explicitly as the
composite of the right tensor inclusion and the fraction-ring map. This is the usual
fraction-field action, without an additional choice of an algebra structure.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

set_option autoImplicit false

namespace ValuationRing

/-- A generic algebraic dependence specializes to a relation with a coefficient equal to one.
Source: Stacks Project, Algebra, Tag 00QK,
`lemma-finite-type-domain-over-valuation-ring-dim-fibres`, generic kernel and its reduction
(blueprint: lem-trf-valuation-generic-relation-specialization).

Proof plan:
1. By `lem-weil-pbc-generic-fibre-localization-domain-irreducible`, the generic tensor
   algebra is the localization of the domain `B` at the nonzero elements of `A`. Thus it
   is a nonzero domain, and both `B → B ⊗[A] K` and its map to its fraction field are
   injective. Mathlib supplies `IsLocalization.tensor` and
   `IsLocalization.isDomain_of_le_nonZeroDivisors` for this step.
2. In the fraction field, the images of the `n` variables cannot be algebraically
   independent: their cardinality would force transcendence degree at least `n` by
   `def-kun-transcendence-degree`. Hence there is a nonzero polynomial relation over `K`.
   Repeated images already give a relation `X i - X j`; for `n = 0` the inequality is
   impossible. Use the polynomial ring of `def-weil-pbc-mv-polynomial-ring`.
3. Among its finitely many nonzero coefficients choose `c` with every ratio `c_I / c`
   in `A`. Induct over the coefficient list: retain `c` when `d / c` lies in `A`, and
   otherwise replace it by `d`; the valuation-ring property puts `c / d` in `A`, and
   multiplication preserves all earlier ratios. Dividing gives a polynomial over `A`
   with its selected coefficient exactly `1`.
4. Its evaluation is zero in the fraction field, so injectivity from step 1 gives
   `α h = 0` in `B`; the evaluation formula is the polynomial universal property.
5. Reduce the coefficients using `IsLocalRing.residue A`. The selected coefficient is
   still `1`, so the reduction is nonzero. The tensor bilinearity of
   `def-weil-pbc-module-tensor-product` identifies its residue evaluation with
   `α h ⊗ 1 = 0`. This does not require the residue tensor algebra to be nonzero.
-/
theorem exists_relation_coeff_one_and_residue_relation
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type v) [CommRing B] [IsDomain B] [Algebra A B]
    (hAB : Function.Injective (algebraMap A B))
    (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B) :
    IsDomain (B ⊗[A] K) ∧
      ((@Algebra.trdeg K (FractionRing (B ⊗[A] K)) _ _
          (RingHom.toAlgebra
            ((algebraMap (B ⊗[A] K) (FractionRing (B ⊗[A] K))).comp
              (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := K)).toRingHom)))
          < (n : Cardinal) →
        ∃ h : MvPolynomial (Fin n) A,
          α h = 0 ∧
          (∃ I : Fin n →₀ ℕ, MvPolynomial.coeff I h = 1) ∧
          MvPolynomial.map (IsLocalRing.residue A) h ≠ 0 ∧
          MvPolynomial.eval₂Hom
              (Algebra.TensorProduct.includeRight
                (R := A) (A := B) (B := IsLocalRing.ResidueField A)).toRingHom
              (fun i ↦ α (MvPolynomial.X i) ⊗ₜ[A] (1 : IsLocalRing.ResidueField A))
              (MvPolynomial.map (IsLocalRing.residue A) h) = 0) := by
  sorry

end ValuationRing
