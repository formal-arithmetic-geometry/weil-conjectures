module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Perfect

import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Common finite extensions of finitely many complete traits

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV, §4.2.3,
the finite common base change dominating the finitely many Epp extensions
(blueprint: lem-per-epp-common-finite-trait-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x t

namespace IsDiscreteValuationRing

/-- Finitely many complete DVR extensions with finite fraction-field extensions admit
one finite complete DVR extension receiving local embeddings from them all.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV, §4.2.3,
sentence beginning "De tels ideaux p etant en nombre fini"
(blueprint: lem-per-epp-common-finite-trait-extension).

Proof:
1. Enumerate the finite family. Starting with K0, embed the field constructed so far
   and the next Ki into a common field using [lem-weil-common-extension-fields].
   Their compositum is finite by [lem-weil-pbc-compositum-degree-bound]. Products
   of spanning elements show finiteness over K0 at each step. For an empty family
   take K0 itself. This produces a finite L/K0 with compatible embeddings Ki → L.
2. Normalize W0 in L using [def-weil-pbc-integral-closure] and
   [lem-per-complete-dvr-finite-normalization]. The resulting W is a complete DVR,
   finite over W0, with local injective structure map. The uniqueness assertion
   identifies each Wi with the normalization of W0 in Ki. Transporting monic
   equations along Ki → L gives injective W0-algebra maps Wi → W.
3. Write the image of a base uniformizer as a unit times a positive power of a
   uniformizer of Wi, using [lem-weil-pbc-dvr-unit-times-uniformizer-power]. Its
   image in W is a nonunit. Primality of the maximal ideal forces the uniformizer
   of Wi to map into that ideal. Units map to units, so each Wi → W is local.
4. Reduce a finite W0-module spanning family of W modulo its maximal ideal.
   Its images span the residue field over the residue field of W0, proving that
   the canonical residue-field map is finite.
5. Finite-dimensionality implies algebraicity by linear dependence of powers.
   Apply [lem-per-algebraic-extension-perfect] to get perfectness when the base
   residue field is perfect. This includes the empty-family case. -/
theorem exists_common_finite_trait_extension
    (W0 : Type u) [CommRing W0] [IsDomain W0] [IsDiscreteValuationRing W0]
    [IsAdicComplete (IsLocalRing.maximalIdeal W0) W0]
    (K0 : Type v) [Field K0] [Algebra W0 K0] [IsFractionRing W0 K0]
    (I : Type t) [Finite I] (Wi : I → Type w)
    [∀ i : I, CommRing (Wi i)] [∀ i : I, IsDomain (Wi i)]
    [∀ i : I, IsDiscreteValuationRing (Wi i)]
    [∀ i : I, IsAdicComplete (IsLocalRing.maximalIdeal (Wi i)) (Wi i)]
    [∀ i : I, Algebra W0 (Wi i)]
    [∀ i : I, IsLocalHom (algebraMap W0 (Wi i))]
    (hinj : ∀ i : I, Function.Injective (algebraMap W0 (Wi i)))
    (Ki : I → Type x) [∀ i : I, Field (Ki i)]
    [∀ i : I, Algebra (Wi i) (Ki i)] [∀ i : I, IsFractionRing (Wi i) (Ki i)]
    [∀ i : I, Algebra K0 (Ki i)] [∀ i : I, Module.Finite K0 (Ki i)]
    (hK : ∀ (i : I) (a : W0),
      algebraMap (Wi i) (Ki i) (algebraMap W0 (Wi i) a) =
        algebraMap K0 (Ki i) (algebraMap W0 K0 a)) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W)
      (_ : IsDiscreteValuationRing W) (_ : Algebra W0 W)
      (_ : IsLocalHom (algebraMap W0 W)),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
      Function.Injective (algebraMap W0 W) ∧ Module.Finite W0 W ∧
      (∀ i : I, ∃ f : Wi i →ₐ[W0] W,
        Function.Injective f ∧ IsLocalHom f.toRingHom) ∧
      RingHom.Finite (IsLocalRing.ResidueField.map (algebraMap W0 W)) ∧
      (PerfectField (IsLocalRing.ResidueField W0) →
        PerfectField (IsLocalRing.ResidueField W)) := by
  sorry

end IsDiscreteValuationRing
