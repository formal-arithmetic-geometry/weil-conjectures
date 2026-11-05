/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RepresentationTheory.Intertwining
public import WeilConjectures.RepresentationTheory.FiniteDimensionalRealization

/-!
# Functors between categories of representations

* `Rep.uliftFunctor`: the universe lift `Rep.{w} k G ⥤ Rep.{max w w'} k G`, `V ↦ ULift V`;
* `Rep.tprodFunctor`: the tensor product `(V, W) ↦ V ⊗ W` of representations, as a bifunctor
  (the category `Rep.{w} k G` is only monoidal in Mathlib when `w` is the universe of `k`);
* `Representation.Equiv.tprodEquivLinHomOfDual_map`: the naturality of the identification
  `ρ ⊗ σ ≅ Hom(ρ', σ)` for `ρ' ≅ ρ^∨`.
-/

@[expose] public section

universe w w' v

open CategoryTheory

namespace Rep

variable (k : Type v) [CommRing k] (G : Type*) [Monoid G]

end Rep

namespace Representation

variable {k G V V' W W₂ V₂ V₂' : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W] [Module k W] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₂'] [Module k V₂'] [AddCommGroup W₂] [Module k W₂]
  {ρ : Representation k G V} {ρ' : Representation k G V'} {σ : Representation k G W}
  {ρ₂ : Representation k G V₂} {ρ₂' : Representation k G V₂'} {σ₂ : Representation k G W₂}

end Representation
