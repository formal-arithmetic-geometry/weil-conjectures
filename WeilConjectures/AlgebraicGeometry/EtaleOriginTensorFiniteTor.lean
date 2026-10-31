/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Finite-Tor tensor preserves bounded-below etale origin

Source: the current blueprint lem-pur-coprojection, test-object Hom calculation
(blueprint: lem-pur-etale-origin-tensor-finite-tor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private theorem plus_tensor_of_tor_right
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.TStructure.t.plus K)
    (hL : ∃ a b : ℤ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b L) :
    _root_.DerivedCategory.TStructure.t.plus (K ⊗ L) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
  obtain ⟨c, hc⟩ := hK
  obtain ⟨a, b, hL⟩ := hL
  have : K.IsGE c := hc
  have : (L ⊗ K).IsGE (a + c) :=
    _root_.DerivedCategory.isGE_tensor_of_torAmplitudeIn hL K c
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso (β_ L K) ⟨a + c, inferInstance⟩

/-- Tensoring an object bounded below of etale origin by a finite-Tor object of etale
origin preserves that domain.
Source: blueprint lem-pur-coprojection.proof.md, domain checks in the Hom calculation
(blueprint: lem-pur-etale-origin-tensor-finite-tor).

Proof: Choose bounded-below etale representatives for both objects. The strong monoidal
comparison identifies the comparison pullback of their tensor with the desired tensor.
The finite Tor lower bound and the lower bound of the first factor give a lower bound
for this tensor. Exact faithful comparison reflects that lower bound to the etale tensor,
which supplies the required bounded-below etale-origin witness. -/
theorem plusEtaleOrigin_tensor_of_finiteTor
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X L)
    (ht : ∃ a b : ℤ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b L) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X (K ⊗ L) := by
  have hp := plus_tensor_of_tor_right Λ hK.plus ht
  obtain ⟨K₀, _, ⟨eK⟩⟩ := hK
  obtain ⟨L₀, _, ⟨eL⟩⟩ := hL
  let e := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} Λ) K₀).app L₀ ≪≫ tensorIso eK eL
  obtain ⟨a, ha⟩ := hp
  have : (K ⊗ L).IsGE a := ha
  refine ⟨K₀ ⊗ L₀, ⟨a, ?_⟩, ⟨e⟩⟩
  exact isGE_of_isGE_mapDerivedCategory_comparisonUpperStar
    (_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a)

end AlgebraicGeometry.ProEtale
