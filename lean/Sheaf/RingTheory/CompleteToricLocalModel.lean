/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module
public import Sheaf.RingTheory.LogRegularSaturationNormality

/-!
# Complete toric local models with a chart

Source: ILO, Travaux de Gabber, Exposé VI 1.6(i)--(ii), printed p. 70
(blueprint: def-trf-complete-toric-local-model).
The ring `B_L(P,n)` and its boundary ideal are the published
`AddMonoidAlgebra.CompletedLocalModel` and `completedLocalModelBoundaryIdeal`
of lem-trf-log-regular-saturation-normality; only the predicate is new here.
-/

@[expose] public section

universe uC uP uR

namespace AddMonoidAlgebra

/-- `R` with the chart `z` is one of the two complete toric local models: (i)
`B_k(P,n)` for a field `k`, or (ii) `B_C(P,n)/(θ)` for a Cohen ring `C` of residue
characteristic `p` with `θ - p ∈ (z^q (q ≠ 0), t₁, …, tₙ)`, by a ring isomorphism
carrying the monomial `z^q` of the model to `z q`.
Source: ILO VI 1.6(i)--(ii), p. 70
(blueprint: def-trf-complete-toric-local-model). -/
def IsCompleteToricLocalModel {P : Type uP} [AddCommMonoid P] (n : ℕ)
    (R : Type uR) [CommRing R] (z : P → R) : Prop :=
  (∃ (k : Type uC) (_ : Field k) (e : CompletedLocalModel k P n ≃+* R),
    ∀ q : P, z q = e (algebraMap (MvPolynomial (Fin n) (AddMonoidAlgebra k P))
      (CompletedLocalModel k P n) (MvPolynomial.C (single q (1 : k))))) ∨
  (∃ (C : Type uC) (_ : CommRing C) (_ : IsLocalRing C) (p : ℕ),
    IsCohenRing p C ∧ ∃ θ : CompletedLocalModel C P n,
      θ - (p : CompletedLocalModel C P n) ∈ completedLocalModelBoundaryIdeal C P n ∧
      ∃ e : (CompletedLocalModel C P n ⧸ Ideal.span {θ}) ≃+* R,
        ∀ q : P, z q = e (Ideal.Quotient.mk (Ideal.span {θ})
          (algebraMap (MvPolynomial (Fin n) (AddMonoidAlgebra C P))
            (CompletedLocalModel C P n) (MvPolynomial.C (single q (1 : C))))))

end AddMonoidAlgebra
