/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdicCompleteHomology
public import WeilConjectures.CategoryTheory.Sites.DerivedAdicComplete
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CountableProducts
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
public import WeilConjectures.Topology.ContinuousMapAdicTower

/-!
# Finitely presented `𝒪_{E,V}`-modules are derived complete

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `V` a scheme.

- The sections of `𝒪_{E,V}` over `W ∈ V_proét` are the continuous maps `W → 𝒪_E` (Bhatt–Scholze,
  Lemma 4.2.12, `ProEtale.isIso_continuousMapComparison`), and on `C(W, 𝒪_E)^ℕ` the map
  `(xᵢ) ↦ (xᵢ - ℓ xᵢ₊₁)` is bijective (`ContinuousMap.bijective_sub_zsmul_succ`). Hence the
  regular module `𝒪_{E,V}` is derived `ℓ`-adically complete
  (`ProEtale.isDerivedAdicComplete_regular_padicIntegers`).
- Derived complete objects of an abelian category with exact countable products are stable
  under finite direct sums and cokernels (`CategoryTheory.IsDerivedAdicComplete.biproduct`,
  `DerivedCategory.isDerivedAdicComplete_cokernel`), so every finitely presented
  `𝒪_{E,V}`-module is derived `ℓ`-adically complete
  (`ProEtale.isDerivedAdicComplete_of_isFinitelyPresented`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

section

variable {X : Scheme.{u}} (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

end

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

end AlgebraicGeometry.ProEtale
