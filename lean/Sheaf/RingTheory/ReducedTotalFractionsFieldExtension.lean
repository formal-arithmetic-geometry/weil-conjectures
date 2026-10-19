/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Reduced total fractions under extension of the ground field

Source: Stacks Project, Tag 0C3N, proof of `lemma-normalization-and-change-of-fields`,
second paragraph (blueprint: lem-per-reduced-total-fractions-field-extension).
The maps are specified by unique existence and their values on generators. Thus the
statements include their canonicity without choosing maps from an existence proof.
-/

@[expose] public section

noncomputable section

universe u v w t

open scoped TensorProduct

namespace Algebra

/-- The reduction of the scalar extension, using Mathlib's quotient by the nilradical.
Source: Stacks 0C3N (blueprint: lem-per-reduced-total-fractions-field-extension). -/
abbrev ReducedScalarExtension (k : Type u) (A : Type v) (L : Type w)
    [CommRing k] [CommRing A] [CommRing L] [Algebra k A] [Algebra k L] :=
  (A ⊗[k] L) ⧸ nilradical (A ⊗[k] L)

/-- The quotient map to the reduced scalar extension.
Source: Stacks 0C3N (blueprint: lem-per-reduced-total-fractions-field-extension). -/
def reducedScalarExtensionClass (k : Type u) (A : Type v) (L : Type w)
    [CommRing k] [CommRing A] [CommRing L] [Algebra k A] [Algebra k L] :
    A ⊗[k] L →+* ReducedScalarExtension k A L :=
  Ideal.Quotient.mk (nilradical (A ⊗[k] L))

/-- The canonical map from the tensor algebra to the total fractions of its reduction.
`FractionRing` denotes total fractions even when the ring is not a domain.
Source: Stacks 0C3N (blueprint: lem-per-reduced-total-fractions-field-extension). -/
def scalarExtensionToReducedFractions (k : Type u) (A : Type v) (L : Type w)
    [CommRing k] [CommRing A] [CommRing L] [Algebra k A] [Algebra k L] :
    A ⊗[k] L →+* FractionRing (ReducedScalarExtension k A L) :=
  (algebraMap (ReducedScalarExtension k A L)
    (FractionRing (ReducedScalarExtension k A L))).comp (reducedScalarExtensionClass k A L)

/-- The fraction formula `theta ((b/s) tensor lambda) = j (b tensor lambda) / j (s tensor 1)`.
It is written after multiplication by the denominator, whose image is a unit for the
canonical maps below. This also applies to a principal localization, with its fraction
field identified with `FractionRing A`.
Source: Stacks 0C3N (blueprint: lem-per-reduced-total-fractions-field-extension). -/
def TensorFractionFormula (k : Type u) (A : Type v) (L : Type w) (Q : Type t)
    [Field k] [CommRing A] [IsDomain A] [Field L] [CommRing Q]
    [Algebra k A] [Algebra k L] (j : A ⊗[k] L →+* Q)
    (theta : FractionRing A ⊗[k] L →+* Q) : Prop :=
  ∀ (b s : A), s ≠ 0 → ∀ l : L,
    theta ((algebraMap A (FractionRing A) b / algebraMap A (FractionRing A) s) ⊗ₜ[k] l) *
      j (s ⊗ₜ[k] (1 : L)) = j (b ⊗ₜ[k] l)

/-- The canonical comparison from the extended fraction field has precisely nilpotent
kernel; the comparisons commute with field towers and principal localization.
The generator formulas determine the maps uniquely.
Source: Stacks 0C3N, second proof paragraph
(blueprint: lem-per-reduced-total-fractions-field-extension).

Proof (the node's steps):
1. For `k ⊆ L ⊆ M` the scalar map `B_L = A ⊗ L → B_M` is injective (an `L`-basis of `M`
containing `1` gives a retraction of `b ↦ b ⊗ 1`). It is flat: `M` is flat over the field
`L` (lem-weil-pbc-module-over-field-flat), `B_M ≅ B_L ⊗_L M`, and flatness is stable
under base change (lem-weil-pbc-flat-module-base-change). A nilpotent image comes from
a nilpotent element, so `R_L → R_M` is defined and injective. By going down for the flat
map (lem-sc-flat-going-down), a minimal prime of `B_M` contracts to a minimal prime of
`B_L`; minimal primes are unchanged by reduction. In a reduced ring the zerodivisors
are the union of the minimal primes
(lem-weil-pbc-reduced-zerodivisors-union-minimal-primes), so a nonzerodivisor of `R_L`
maps to a nonzerodivisor of `R_M`.
2. Hence `S_L` maps into `S_M`, and the localization universal property gives
`Q_L → Q_M`, `c/d ↦ c̄/d̄`. If a fraction maps to zero, a nonzerodivisor of `R_M` kills
the image of its numerator, so that image vanishes and, by injectivity of
`R_L → R_M`, the numerator vanishes: `Q_L → Q_M` is injective.
3. For `s ≠ 0` in the domain `A`, multiplication by `s` stays injective on `B_L`, so
`s ⊗ 1` is regular in `B_L`; if `(s ⊗ 1) b` is nilpotent, a power of `s ⊗ 1` kills a
power of `b`, so `b` is nilpotent and `s ⊗ 1` stays regular in `R_L`. The map
`(a/s, λ) ↦ (a ⊗ λ)/(s ⊗ 1)` is well defined (`as' = a's` in `A`) and `k`-bilinear;
the tensor universal property gives the ring map `θ_L` with this formula. It restricts
to `B_L → R_L → Q_L` and satisfies `θ_L((1/s) z) = (s ⊗ 1)⁻¹ θ_L(z)`.
4. Every element of `F ⊗ L` is `(1/s) ι(b)` with `b ∈ B_L` and `s ∈ A` nonzero. If
`θ_L` kills it, a nonzerodivisor of `R_L` kills `b̄`, so `b̄ = 0`, `b` is nilpotent and so
is `(1/s) ι(b)`. Conversely `Q_L`, a localization of the reduced ring `R_L`, is reduced,
so nilpotents map to zero: the kernel is the nilradical. Fractions and pure tensors
generate the source, so the formula determines `θ_L`.
5. All maps are induced by the structural tensor, reduction and localization maps and send
a represented fraction to the fraction of its image. Associativity of tensor products
gives the tower square; for nonzero `a`, `a ⊗ 1` is regular, so the total fractions of
the reduction of `A[1/a] ⊗ L` are canonically those of `R_L` (mutually inverse maps from
the localization universal property), and `Frac(A[1/a]) = Frac(A)`. The localized
comparison is then given by the same formula, with nilpotent kernel by step 4, and the
compatibilities follow by uniqueness on fraction pure tensors. -/
theorem reduced_total_fractions_field_extension
    (k : Type u) (A : Type v)
    [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (hA : RingHom.FiniteType (algebraMap k A)) :
    (∀ (L : Type w) [Field L] [Algebra k L],
      ∃! theta : FractionRing A ⊗[k] L →+* FractionRing (ReducedScalarExtension k A L),
        TensorFractionFormula k A L _ (scalarExtensionToReducedFractions k A L) theta ∧
        RingHom.ker theta = nilradical (FractionRing A ⊗[k] L)) ∧
    (∀ (L : Type w) (M : Type t) [Field L] [Field M] [Algebra k L] [Algebra k M]
        [Algebra L M] [IsScalarTower k L M],
      ∃! r : ReducedScalarExtension k A L →+* ReducedScalarExtension k A M,
        (∀ x : A ⊗[k] L,
          r (reducedScalarExtensionClass k A L x) = reducedScalarExtensionClass k A M
            (Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k L M) x)) ∧
        Function.Injective r ∧
        (∀ s ∈ nonZeroDivisors (ReducedScalarExtension k A L),
          r s ∈ nonZeroDivisors (ReducedScalarExtension k A M)) ∧
        ∃! q : FractionRing (ReducedScalarExtension k A L) →+*
            FractionRing (ReducedScalarExtension k A M),
          (∀ x : ReducedScalarExtension k A L,
            q (algebraMap _ (FractionRing (ReducedScalarExtension k A L)) x) =
              algebraMap _ (FractionRing (ReducedScalarExtension k A M)) (r x)) ∧
          Function.Injective q ∧
          (∀ (x : ReducedScalarExtension k A L)
              (s : nonZeroDivisors (ReducedScalarExtension k A L)),
            q (Localization.mk x s) =
              algebraMap _ (FractionRing (ReducedScalarExtension k A M)) (r x) *
                Ring.inverse (algebraMap _ (FractionRing (ReducedScalarExtension k A M)) (r s))) ∧
          (∀ (thetaL : FractionRing A ⊗[k] L →+* FractionRing (ReducedScalarExtension k A L))
              (thetaM : FractionRing A ⊗[k] M →+* FractionRing (ReducedScalarExtension k A M)),
            TensorFractionFormula k A L _ (scalarExtensionToReducedFractions k A L) thetaL →
            TensorFractionFormula k A M _ (scalarExtensionToReducedFractions k A M) thetaM →
            q.comp thetaL = thetaM.comp
              (Algebra.TensorProduct.map (AlgHom.id k (FractionRing A))
                (IsScalarTower.toAlgHom k L M)).toRingHom)) ∧
    (∀ (L : Type w) [Field L] [Algebra k L] (a : A) (ha : a ≠ 0),
      ∃! e : FractionRing (ReducedScalarExtension k A L) ≃+*
          FractionRing (ReducedScalarExtension k (Localization.Away a) L),
        (∀ (b : A) (l : L),
          e (scalarExtensionToReducedFractions k A L (b ⊗ₜ[k] l)) =
            scalarExtensionToReducedFractions k (Localization.Away a) L
              (algebraMap A (Localization.Away a) b ⊗ₜ[k] l)) ∧
        ∃! thetaLocal : FractionRing A ⊗[k] L →+*
            FractionRing (ReducedScalarExtension k (Localization.Away a) L),
          TensorFractionFormula k A L _
            ((scalarExtensionToReducedFractions k (Localization.Away a) L).comp
              (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A (Localization.Away a))
                (AlgHom.id k L)).toRingHom) thetaLocal ∧
          RingHom.ker thetaLocal = nilradical (FractionRing A ⊗[k] L) ∧
          (∀ theta : FractionRing A ⊗[k] L →+* FractionRing (ReducedScalarExtension k A L),
            TensorFractionFormula k A L _ (scalarExtensionToReducedFractions k A L) theta →
            e.toRingHom.comp theta = thetaLocal)) := by
  sorry

end Algebra
