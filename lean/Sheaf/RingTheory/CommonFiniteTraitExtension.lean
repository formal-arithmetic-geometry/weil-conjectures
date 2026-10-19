/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q152
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.FieldTheory.Perfect

import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# A common finite extension of finitely many complete traits

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, §4.2.3,
“De tels idéaux p étant en nombre fini”
(blueprint: lem-per-epp-common-finite-trait-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u u₁ v v₁ w

open IsLocalRing

namespace IsDiscreteValuationRing

/-- Finitely many finite complete trait extensions have a common finite complete trait
extension. The compatibility `hK` makes each fraction-field extension the one induced
by the specified base map. Residue-field finiteness is for the induced residue map.

Source: ILO, Travaux de Gabber, Exposé IV, §4.2.3, the common finite base change
in the sentence “De tels idéaux p étant en nombre fini”.
(blueprint: lem-per-epp-common-finite-trait-extension).

Proof:
1. Enumerate the finite family. Starting from K₀, repeatedly use
   lem-weil-common-extension-fields and take the compositum with the next Kᵢ.
   The compositum-degree bound lem-weil-pbc-compositum-degree-bound makes each
   step finite; products of spanning elements make the total extension finite.
   This gives a finite L/K₀ receiving all Kᵢ. For the empty family take L = K₀.
2. Take the integral closure W of W₀ in L (def-weil-pbc-integral-closure).
   By lem-per-complete-dvr-finite-normalization, W is a complete DVR, finite over
   W₀, and the base map is injective and local. The uniqueness clause identifies
   Wᵢ with the integral closure of W₀ in Kᵢ. Transporting monic equations along
   the embeddings Kᵢ → L restricts them to injective W₀-algebra maps Wᵢ → W.
3. Write the image of a base uniformizer as a unit times a positive power of a
   uniformizer of Wᵢ (lem-weil-pbc-dvr-unit-times-uniformizer-power). Its image
   lies in the maximal ideal of W. Primality implies that the image of the Wᵢ
   uniformizer also lies there. Nonunits therefore map to nonunits, while units
   map to units. Each Wᵢ → W is local.
4. Reduce a finite set of W₀-module generators of W modulo its maximal ideal.
   Their residue classes span the residue field over ResidueField W₀.
5. A finite field extension is algebraic by linear dependence among powers.
   If the base residue field is perfect, lem-per-algebraic-extension-perfect
   makes the new residue field perfect as well. -/
theorem exists_common_finite_trait_extension
    (W₀ : Type u) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀]
    (K₀ : Type u₁) [Field K₀] [Algebra W₀ K₀] [IsFractionRing W₀ K₀]
    (I : Type w) [Finite I] (Wᵢ : I → Type v) (Kᵢ : I → Type v₁)
    [∀ i : I, CommRing (Wᵢ i)] [∀ i : I, IsDomain (Wᵢ i)]
    [∀ i : I, IsDiscreteValuationRing (Wᵢ i)]
    [∀ i : I, IsAdicComplete (maximalIdeal (Wᵢ i)) (Wᵢ i)]
    [∀ i : I, Algebra W₀ (Wᵢ i)]
    [∀ i : I, IsLocalHom (algebraMap W₀ (Wᵢ i))]
    (hinj : ∀ i : I, Function.Injective (algebraMap W₀ (Wᵢ i)))
    [∀ i : I, Field (Kᵢ i)] [∀ i : I, Algebra (Wᵢ i) (Kᵢ i)]
    [∀ i : I, IsFractionRing (Wᵢ i) (Kᵢ i)]
    [∀ i : I, Algebra K₀ (Kᵢ i)] [∀ i : I, Module.Finite K₀ (Kᵢ i)]
    (hK : ∀ i : I, (algebraMap (Wᵢ i) (Kᵢ i)).comp (algebraMap W₀ (Wᵢ i)) =
      (algebraMap K₀ (Kᵢ i)).comp (algebraMap W₀ K₀)) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (_ : Algebra W₀ W)
      (_ : IsLocalHom (algebraMap W₀ W)),
      Function.Injective (algebraMap W₀ W) ∧ Module.Finite W₀ W ∧
      (∀ i : I, ∃ f : Wᵢ i →ₐ[W₀] W, Function.Injective f ∧ IsLocalHom f.toRingHom) ∧
      (ResidueField.map (algebraMap W₀ W)).Finite ∧
      (PerfectField (ResidueField W₀) → PerfectField (ResidueField W)) := by
  sorry

end IsDiscreteValuationRing
