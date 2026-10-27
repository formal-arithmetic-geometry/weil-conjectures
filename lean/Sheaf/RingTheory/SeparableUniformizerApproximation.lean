module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Separable approximation to a uniformizer root

Source: Stacks Project, More on Algebra, Tag 09EW (lemma-make-degree-q-extension),
in characteristic `p` with `q = p`; the second approximation is used in Tag 09EY.
(blueprint: lem-sfb-epp-separable-uniformizer-approximation)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsDiscreteValuationRing

/-- A complete DVR of characteristic `p` admits a separable extension of degree `p`
whose complete DVR integral closure has a uniformizer `s` satisfying
`t = s ^ p + s ^ (n * p) * a`. The residue isomorphism is induced by the inclusion,
as specified by its values on all quotient representatives, and `(t)R' = (s)^p`.

Source: Stacks Project, More on Algebra, Tag 09EW (lemma-make-degree-q-extension),
equicharacteristic case with `q = p`, and Tag 09EY (lemma-purely-inseparable-case).
Completeness is the finite-normalization specialization over a complete DVR.
(blueprint: lem-sfb-epp-separable-uniformizer-approximation)

Proof:
1. Apply lem-sfb-epp-approximate-uniformizer-root with `E = F`, `pi = t`, `r = 1`
   and `h = n`. Primeness, characteristic, completeness and the uniformizer
   hypotheses are the stated ones. Since `p ^ 1 = p`, this gives a separable
   extension `F'/F` of degree `p`, its complete DVR integral closure `R'`, unchanged
   residue field, maximal-ideal extension equal to the `p`th power, and
   `s ^ p = t + s ^ (n * p) * b'` for some `b'` in `R'`.
2. Set `a = -b'` and rearrange, also in characteristic two. By
   def-sc-discrete-valuation-ring the maximal ideals are precisely `(t)` and `(s)`.
   The supplied residue-field identification is therefore the induced quotient
   isomorphism, and the ideal equality becomes `(t)R' = (s)^p`.
-/
theorem exists_separable_uniformizer_approximation
    (p : ℕ) (hp : p.Prime)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharP R p] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (n : ℕ) (hn : 1 < n) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra F L) (_ : Algebra R L)
      (_ : IsScalarTower R F L) (_ : Module.Finite F L) (_ : Algebra.IsSeparable F L)
      (hS : IsDiscreteValuationRing (integralClosure R L)),
      Module.finrank F L = p ∧
      IsAdicComplete
        (@IsLocalRing.maximalIdeal (integralClosure R L) _ hS.toIsLocalRing)
        (integralClosure R L) ∧
      ∃ s a : integralClosure R L,
        @IsLocalRing.maximalIdeal (integralClosure R L) _ hS.toIsLocalRing =
          Ideal.span {s} ∧
        algebraMap R (integralClosure R L) t = s ^ p + s ^ (n * p) * a ∧
        (∃ e : R ⧸ Ideal.span {t} ≃+* (integralClosure R L) ⧸ Ideal.span {s},
          ∀ x : R, e (Ideal.Quotient.mk (Ideal.span {t}) x) =
            Ideal.Quotient.mk (Ideal.span {s}) (algebraMap R (integralClosure R L) x)) ∧
        Ideal.map (algebraMap R (integralClosure R L)) (Ideal.span {t}) =
          (Ideal.span {s}) ^ p := by
  sorry

end IsDiscreteValuationRing
