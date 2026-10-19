/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.Category
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient
import Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds
import Sheaf.Paper.AdicPunctualWeights

/-! # Stability of mixed upper weight bounds

Source: Weil-conjectures blueprint, sec-deligne-laumon-general/sk-d-dl-general-weights,
main-20261015, lemma lem-a1-mixed-direct-summand, order 3155
(blueprint: lem-a1-mixed-direct-summand).

## Main statements

- The imported sheaf `of_mono`, `of_epi`, `of_shortExact`, and `of_retract` give
  subobjects, quotients, extensions, and direct summands.
- `FrobeniusModule.mixedOfWeightsAtMost_stability`: the analogous assertions for the
  recorded finite stable-filtration definition of mixed Frobenius modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u₁ u₂ u₃ v

namespace FrobeniusModule

/-- The same four stability assertions for finite-dimensional Frobenius modules,
using mixedness defined by a finite stable filtration, with no semisimplicity assumption.
An equivariant split inclusion and projection express a direct summand.

Source: blueprint main-20261015, sec-deligne-laumon-general/sk-d-dl-general-weights,
lemma lem-a1-mixed-direct-summand, final paragraph
(blueprint: lem-a1-mixed-direct-summand).

Proof: for an injective equivariant map identify its source with the stable image,
and use lem-a1-subquotient-extension-bounds. For a surjective equivariant map identify
its target with the quotient by the stable kernel, and apply the same lemma. Given
an exact sequence, concatenate the image of a mixed filtration of the first term
with inverse images of a mixed filtration of the last term; exactness identifies
the successive quotients. This is lem-a1-extension-bounds. Finally a split inclusion
is injective, so the subobject assertion applies. Equivalently all three filtration
arguments for Weil sheaves apply directly to stable vector subspaces. They cover the
zero module, empty filtrations, repeated filtration terms, and nonsemisimple Frobenius.
-/
theorem mixedOfWeightsAtMost_stability
    (p a ell : ℕ) [Fact p.Prime] (ha : 1 ≤ a)
    [Fact ell.Prime] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra ℚ_[ell] Qlb] (hQ : IsAlgClosure ℚ_[ell] Qlb)
    (iota : Qlb ≃+* ℂ) (w : ℝ) :
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (f : A.carrier →ₗ[Qlb] B.carrier),
      (∀ x : A.carrier, f (A.frobenius x) = B.frobenius (f x)) →
      Function.Injective f →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w) ∧
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (g : A.carrier →ₗ[Qlb] B.carrier),
      (∀ x : A.carrier, g (A.frobenius x) = B.frobenius (g x)) →
      Function.Surjective g →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w) ∧
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (C : FrobeniusModule.{u₃, v} Qlb)
      (f : A.carrier →ₗ[Qlb] B.carrier) (g : B.carrier →ₗ[Qlb] C.carrier),
      (∀ x : A.carrier, f (A.frobenius x) = B.frobenius (f x)) →
      (∀ x : B.carrier, g (B.frobenius x) = C.frobenius (g x)) →
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota C w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w) ∧
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (i : A.carrier →ₗ[Qlb] B.carrier) (r : B.carrier →ₗ[Qlb] A.carrier),
      (∀ x : A.carrier, i (A.frobenius x) = B.frobenius (i x)) →
      (∀ x : B.carrier, r (B.frobenius x) = A.frobenius (r x)) →
      r.comp i = LinearMap.id →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w) := by
  sorry

end FrobeniusModule
