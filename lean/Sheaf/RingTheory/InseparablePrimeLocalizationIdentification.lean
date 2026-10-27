module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Prime localization after purely inseparable scalar extension

Source: Stacks Project, Varieties, Tag 035W, first paragraph of the proof, using Algebra,
Tags 0BRA, 00E9, 00DK and 00CP
(blueprint: lem-trf-inseparable-prime-localization-identification).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- The canonical scalar extension of `R → R_p`, sending `r ⊗ e` to `(r/1) ⊗ e`.
Source: Stacks Project, Algebra, Tags 00DK and 00CP; Varieties, Tag 035W
(blueprint: lem-trf-inseparable-prime-localization-identification). -/
noncomputable def primeLocalizationBaseChangeMap
    (k : Type u) (E : Type v) (R : Type w)
    [Field k] [Field E] [CommRing R] [Algebra k E] [Algebra k R]
    (p : Ideal R) [p.IsPrime] :
    R ⊗[k] E →+* Localization.AtPrime p ⊗[k] E :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R (Localization.AtPrime p))
    (AlgHom.id k E)).toRingHom

/-- Contraction is an order bijection on spectra after finite purely inseparable base change.
The scalar extension of `R_p` is local; its unique maximal ideal is the unique prime over
that of `R_p`. At every prime `P` over `p`, the canonical map identifies `(R ⊗ E)_P`
with `R_p ⊗ E`, with its fraction formula and compatibility with `R ⊗ E`, `R_p`, and
all maps to an arbitrary ring inverting the complement of `P`.

Source: Stacks Project, Varieties, Tag 035W, first proof paragraph; Algebra, Tags 0BRA,
00E9, 00E0, 00DK, 00D2 and 00CP
(blueprint: lem-trf-inseparable-prime-localization-identification).

Proof plan:
1. Apply lem-pc-homeo-pure-insep to Spec B, for B = R and B = R_p, and use
   lem-weil-pbc-fibre-product-affine-spectra. Contraction is a homeomorphism.
   The closure of a prime is V(prime), so it preserves inclusion in both directions.
2. Every prime of R_p lies in its maximal ideal. Transfer this assertion through
   the order bijection. By lem-weil-pbc-proper-ideal-contained-in-maximal, the prime
   over that maximal ideal is maximal and is the only maximal ideal upstairs.
3. Apply lem-weil-pbc-localization-tensor-over-base with base k, algebra R,
   module R, denominator set R minus p and second module E. Its identification
   respects products and one on pure tensors, and then on finite sums. Thus the
   displayed map makes R_p tensor E the ring localization at these denominators,
   by lem-weil-pbc-ring-localization-universal-property.
4. The inverse image of the unique maximal ideal is a prime of R tensor E over p,
   using lem-trf-localization-maximal-contraction. Step 1 makes this prime equal P.
5. By lem-weil-pbc-local-ring-unit-criterion every element outside P maps to a unit.
   The localization universal property gives theta with the fraction formula.
   Conversely the images of R minus p avoid P, giving an inverse map by step 3.
   Both composites are identities by uniqueness for the two localizations.
6. The construction agrees with the maps from R tensor E. On a fraction r/v of R_p
   it sends (r tensor 1)/(v tensor 1) to (r/v) tensor 1, giving R_p compatibility.
   For any ring D and map inverting the complement of P, extend through both
   localizations. The extensions agree under theta by the same uniqueness argument. -/
theorem inseparable_primeLocalization_identification
    (k : Type u) (E : Type v) (R : Type w)
    [Field k] [Field E] [CommRing R] [Algebra k E] [Algebra k R]
    [Module.Finite k E] [IsPurelyInseparable k E] (p : Ideal R) [p.IsPrime] :
    (∃ e : PrimeSpectrum (Localization.AtPrime p ⊗[k] E) ≃o
        PrimeSpectrum (Localization.AtPrime p),
      ∀ q, e q = PrimeSpectrum.comap
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime p ⊗[k] E)) q) ∧
    IsLocalRing (Localization.AtPrime p ⊗[k] E) ∧
    ∃ n : Ideal (Localization.AtPrime p ⊗[k] E),
      n.IsMaximal ∧
      (∀ n' : Ideal (Localization.AtPrime p ⊗[k] E), n'.IsMaximal → n' = n) ∧
      n.comap (algebraMap (Localization.AtPrime p) (Localization.AtPrime p ⊗[k] E)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      (∀ q : Ideal (Localization.AtPrime p ⊗[k] E), q.IsPrime →
        q.comap (algebraMap (Localization.AtPrime p) (Localization.AtPrime p ⊗[k] E)) =
          IsLocalRing.maximalIdeal (Localization.AtPrime p) → q = n) ∧
      ∀ (P : Ideal (R ⊗[k] E)) [P.IsPrime],
        P.comap (algebraMap R (R ⊗[k] E)) = p →
        n.comap (primeLocalizationBaseChangeMap k E R p) = P ∧
        ∃ theta : Localization.AtPrime P ≃+* (Localization.AtPrime p ⊗[k] E),
          theta.toRingHom.comp (algebraMap (R ⊗[k] E) (Localization.AtPrime P)) =
            primeLocalizationBaseChangeMap k E R p ∧
          (∀ (a : R ⊗[k] E) (b : P.primeCompl),
            theta (IsLocalization.mk' (Localization.AtPrime P) a b) =
              primeLocalizationBaseChangeMap k E R p a *
                Ring.inverse (primeLocalizationBaseChangeMap k E R p b)) ∧
          (∃ aMap : Localization.AtPrime p →+* Localization.AtPrime P,
            aMap.comp (algebraMap R (Localization.AtPrime p)) =
              (algebraMap (R ⊗[k] E) (Localization.AtPrime P)).comp
                (algebraMap R (R ⊗[k] E)) ∧
            theta.toRingHom.comp aMap =
              algebraMap (Localization.AtPrime p) (Localization.AtPrime p ⊗[k] E)) ∧
          ∀ (D : Type t) [Ring D] (f : R ⊗[k] E →+* D),
            (∀ b : P.primeCompl, IsUnit (f b)) →
            ∃! maps : ((Localization.AtPrime p ⊗[k] E) →+* D) ×
                (Localization.AtPrime P →+* D),
              maps.1.comp (primeLocalizationBaseChangeMap k E R p) = f ∧
              maps.2.comp (algebraMap (R ⊗[k] E) (Localization.AtPrime P)) = f ∧
              maps.1.comp theta.toRingHom = maps.2 := by
  sorry

end Algebra.TensorProduct
