/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.SeparableDegree
import Sheaf.RingTheory.ValuationRingNormal
import WeilConjectures.RingTheory.FiniteModuleComplete

/-!
# Separable approximate roots of a uniformizer

Source: Stacks Project, More on Algebra, Tag 09EW, `lemma-make-degree-q-extension`,
the equicharacteristic-p case; Algebra, Tags 00MA and 0317 for completeness.
(blueprint: lem-sfb-epp-approximate-uniformizer-root)
-/

@[expose] public section

universe u v

set_option autoImplicit false

namespace IsDiscreteValuationRing

/-- A complete DVR in characteristic p has separable totally ramified extensions of degree
p^r whose uniformizer satisfies both prescribed approximation identities. The residue-field
isomorphism commutes with the canonical maps from R.

Source: Stacks Project, More on Algebra, Tag 09EW, `lemma-make-degree-q-extension`,
characteristic-p proof after y = pi z; Algebra, Tags 00MA and 0317 for completeness.
(blueprint: lem-sfb-epp-approximate-uniformizer-root)

Proof:
1. Put q = p^r, N = h + q - 1 and f = X^q - pi^N X - pi. Since q >= 2, f is
   Eisenstein: all nonleading coefficients lie in (pi), and -pi is not in (pi^2).
   By lem-sfb-eisenstein-quotient-dvr, C = R[X]/(f) is a DVR with uniformizer t = [X].
   By lem-weil-pbc-monic-quotient-free, its R-basis is 1,t,...,t^(q-1).
2. Localizing this basis gives a q-dimensional domain D = E[X]/(f). Multiplication
   by a nonzero element of D is injective, hence surjective, so D is a field. Thus
   E1 = D = Frac(C) = E(t), of degree q, with minimal polynomial f.
3. In characteristic p, f' = -pi^N is a nonzero constant, coprime to f. Thus t is
   separable. Apply lem-trf-simple-separable-field-extension to E(t) to obtain
   Algebra.IsSeparable E E1 (def-weil-pbc-separable-algebraic-extension).
4. The monic equation makes C integral over R. Every element of E1 integral over R
   is integral over C; C is integrally closed by lem-weil-pbc-valuation-ring-normal,
   since a DVR is a valuation ring. Hence integralClosure R E1 is C.
5. The relation is t^q = pi*u, with u = 1 + pi^(N-1)*t a unit. Therefore
   (pi)C = (t)^q. Killing t in the presentation gives C/(t) = R/(pi), compatibly
   with the canonical residue maps, giving the asserted residue-field isomorphism.
6. The DVR R is Noetherian and C is finite free over R. Apply
   lem-weil-pbc-finite-module-complete-over-complete-noetherian to obtain (pi)-adic
   completeness of C. The equality pi^k*C = (t^(q*k)) and cofinality of these powers
   among (t^m) identify the two compatible-sequence limits, giving maximal-adic
   completeness of C = integralClosure R E1 (def-weil-pbc-adically-complete-ring).
7. Set b = pi^(q-1)*t. Then t^q = pi + pi^h*b. Since pi^h = t^(h*q)*u^(-h),
   b' = u^(-h)*b gives the second identity for the same t. -/
theorem exists_separable_approximate_uniformizer_root
    (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharP R p] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : Type v) [Field E] [Algebra R E] [IsFractionRing R E]
    (pi : R) (hpi : Irreducible pi)
    (r : ℕ) (hr : 1 ≤ r) (h : ℕ) (hh : 1 < h) :
    ∃ (E1 : Type v) (_ : Field E1) (_ : Algebra E E1)
      (_ : Algebra R E1) (_ : IsScalarTower R E E1)
      (_ : Algebra.IsSeparable E E1)
      (_ : IsDiscreteValuationRing (integralClosure R E1)),
      Module.finrank E E1 = p ^ r ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure R E1))
        (integralClosure R E1) ∧
      ∃ e : IsLocalRing.ResidueField R ≃+*
          IsLocalRing.ResidueField (integralClosure R E1),
        (∀ x : R, e (IsLocalRing.residue R x) =
          IsLocalRing.residue (integralClosure R E1)
            (algebraMap R (integralClosure R E1) x)) ∧
        Ideal.map (algebraMap R (integralClosure R E1)) (IsLocalRing.maximalIdeal R) =
          IsLocalRing.maximalIdeal (integralClosure R E1) ^ (p ^ r) ∧
        ∃ t b b' : integralClosure R E1, Irreducible t ∧
          t ^ (p ^ r) = algebraMap R (integralClosure R E1) pi +
            algebraMap R (integralClosure R E1) pi ^ h * b ∧
          t ^ (p ^ r) = algebraMap R (integralClosure R E1) pi + t ^ (h * p ^ r) * b' := by
  sorry

end IsDiscreteValuationRing
