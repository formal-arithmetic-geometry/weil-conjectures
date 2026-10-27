/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Sheaf.RingTheory.LocalStandardBasisInvariants
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.AssociatedGradedRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-! # Maximal-ideal order under polynomial localization

Source: Stacks Project, Algebra, Tags 031E and 00NO; Hironaka (1970),
proof of Lemma 14, p.169.
(blueprint: lem-trf-polynomial-localization-order-reflection).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Hironaka

/-- Polynomial localization at a prime above the base maximal ideal is regular local
and reflects every power of the maximal ideal, hence preserves ideal-adic order.
The maximal ideal upstairs is written as the extension of `q`; it equals
`IsLocalRing.maximalIdeal (Localization.AtPrime q)` by
`Localization.AtPrime.map_eq_maximalIdeal`.
Source: Stacks Project, Algebra, Tags 031E and 00NO; Hironaka (1970),
proof of Lemma 14, p.169.
(blueprint: lem-trf-polynomial-localization-order-reflection).

Proof:
1. The finite polynomial algebra and its localization are Noetherian
   (lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian).
   The localization is local and its maximal ideal contracts to the base maximal
   ideal. The polynomial projection is flat (lem-nagata-polynomial-projection-flat);
   def-weil-flat-morphism and lem-weil-pbc-spec-map-stalk-localization identify the
   stalk map with the flat local map from R, since localizing R at its maximal
   ideal changes nothing. Its residue-field map k to L is injective.
2. Coefficient reduction identifies the polynomial quotient by the base maximal
   ideal with the polynomial ring over k (def-weil-pbc-mv-polynomial-ring).
   The quotient-localization comparison (lem-weil-pbc-localization-at-prime-of-quotient)
   identifies the closed fibre with its localization at the image prime. It is
   regular by lem-weil-pbc-polynomial-ring-field-regular-ring. Apply
   lem-weil-pbc-flat-over-regular-with-regular-fibre to deduce regularity upstairs.
3. Let d and e be the dimensions of the base and closed fibre. The flat height
   formula (lem-weil-pbc-flat-height-formula) gives dimension d+e upstairs.
   Choose d base parameters and lifts of e fibre parameters; together they generate
   the upstairs maximal ideal. By lem-weil-pbc-regular-local-cotangent-dimension
   their cotangent classes are a basis, as are the base parameter classes downstairs.
4. Apply lem-sfb-regular-local-graded-cotangent-criterion to the two rings and
   lem-weil-pbc-symmetric-algebra-free-module-polynomial to these bases. Transport
   along basis isomorphisms using lem-weil-pbc-symmetric-algebra-universal-property.
   The actual induced graded map becomes k[X] to L[X,Z], preserving X and sending
   coefficients through the residue-field injection. A nonzero coefficient remains
   nonzero, so this graded map is injective, including empty parameter lists.
5. Induct on a. At zero both ideals are top. If the image of r lies in the
   (a+1)-st power, the inductive hypothesis puts r in the a-th power downstairs.
   Its degree-a class maps to zero, so graded injectivity puts r in the (a+1)-st
   power (def-weil-pbc-associated-graded-ring). The reverse inclusion follows
   by mapping products of elements of the base maximal ideal and their sums.
6. The contraction equalities identify the sets of natural exponents defining
   both adic orders, hence their suprema in ENat. At the zero element both sets
   are all natural numbers and both orders are infinite. Empty variable lists
   and zero-dimensional base or fibre require no change to this argument. -/
theorem polynomialLocalization_orderReflection
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (s : ℕ) (q : Ideal (MvPolynomial (Fin s) R)) [q.IsPrime]
    (hq : q.comap (algebraMap R (MvPolynomial (Fin s) R)) =
      IsLocalRing.maximalIdeal R) :
    IsRegularLocalRing (Localization.AtPrime q) ∧
      (∀ a : ℕ,
        (q.map (algebraMap (MvPolynomial (Fin s) R) (Localization.AtPrime q)) ^ a).comap
          (algebraMap R (Localization.AtPrime q)) = IsLocalRing.maximalIdeal R ^ a) ∧
      (∀ r : R,
        adicOrder (q.map (algebraMap (MvPolynomial (Fin s) R) (Localization.AtPrime q)))
            (algebraMap R (Localization.AtPrime q) r) =
          adicOrder (IsLocalRing.maximalIdeal R) r) := by
  sorry

end Hironaka
