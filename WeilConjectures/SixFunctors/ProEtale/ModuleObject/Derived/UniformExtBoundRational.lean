/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralAcyclic
public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive

/-!
# Helpers for the uniform `Ext` bound for constructible `E`-sheaves, from `𝒪_E`

Blueprint `det-uniform-constructible-ext-rational`, coefficients `E`. Let `E ⊆ ℚ̄_ℓ` be a finite
subextension of `ℚ_ℓ` and `X` a scheme. This file computes `Ext` between extensions of scalars
`E ⊗_{𝒪_E} M₀` of `𝒪_{E,X}`-modules: by adjunction
`Ext^q_E(E ⊗ M₀, E ⊗ B₀) = Ext^q_{𝒪_E}(M₀, E ⊗ B₀)`, and `E ⊗ B₀` is the filtered colimit of
`B₀ --ℓ--> B₀ --ℓ--> ⋯` (`ProEtale.isColimitPadicIntegersRingObjSmulSequenceCocone`), so every
class factors through some `Ext^q_{𝒪_E}(M₀, B₀)`
(`ProEtale.eq_zero_of_extendScalars_padicIntegersToPadicSubfield`). The uniform bound itself is
deduced in `...Derived.UniformExtBoundRationalLattice`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

end CategoryTheory.Adjunction

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] {φ : R ⟶ S} [IsMonHom φ] {n : ℕ}
  {c : ℕ → (R ⟶ S)}

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

end AlgebraicGeometry.ProEtale
