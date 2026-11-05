/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Homology.Additive
/-!
# Models of base-derived tensor cohomology and its localization comparison

Source: Stacks Project, Tag 08IB, lemma-compare-base-change, and Tag 06Y6,
lemma-derived-base-change (blueprint: def-pc-base-derived-tensor-cohomology-model).

The model records a total left derived functor with its universal counit, actual
cohomology objects with their tensor-algebra action, and the comparison maps.
Commuting squares fix the maps; no isomorphism of comparison maps is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB uD v w uS uT

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- (blueprint: def-pc-base-derived-tensor-cohomology-model) Stacks, Tag 06Y6.
Extension of scalars is additive. Proof: its maps send `s ⊗ x` to `s ⊗ f x`;
the sum of two maps thus gives `s ⊗ (f x + g x)`, the sum of their two images.
Tensor induction proves equality on all tensors. -/
@[instance]
theorem baseDerivedTensor_extendScalars_additive
    {S : Type uS} {T : Type uT} [CommRing S] [CommRing T]
    (f : S →+* T) : (extendScalars.{uS, uT, v} f).Additive := by
  refine ⟨?_⟩
  intro M N g h
  apply ExtendScalars.hom_ext
  intro m
  change (1 : T) ⊗ₜ[S, f] (g m + h m) =
    (extendScalars f).map g ((1 : T) ⊗ₜ[S, f] m) +
      (extendScalars f).map h ((1 : T) ⊗ₜ[S, f] m)
  simp only [ExtendScalars.map_tmul, TensorProduct.tmul_add]

variable (R : Type uR) (A : Type uA) (B : Type uB) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} B)]

end ModuleCat

