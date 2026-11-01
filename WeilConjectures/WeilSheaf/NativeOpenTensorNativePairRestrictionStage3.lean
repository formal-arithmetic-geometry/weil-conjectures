/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData

/-! Fully faithful restriction on native K-flat pairs.
(blueprint: new-sf-native-open-tensor-pair-restriction-stage3) -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u a b

namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] OpenTensorDescentInput.r_add OpenTensorDescentInput.r_lim
  OpenTensorDescentInput.r_colim OpenTensorDescentInput.r_zero

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeTensorTotal
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorModel
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorInsertion
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeIsKFlat
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeTensorMap
  AlgebraicGeometry.Scheme.Hom.geometricFiberMap
  AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius
  AlgebraicGeometry.ProEtale.adicUpperStar
  CategoryTheory.Mod.tensorLeftMap
  AlgebraicGeometry.ProEtaleWeilSheaf.upperStar
  AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- Restriction is fully faithful on pairs of native K-flat representatives. -/
structure NativePairRestrictionData (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ Z) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] where
  fullyFaithful : ((Functor.whiskeringLeft
      (ObjectProperty.FullSubcategory (NativeIsKFlat k₀ l Z) ×
        ObjectProperty.FullSubcategory (NativeIsKFlat k₀ l Z))
      (DerivedCategory (ProEtaleWeilSheaf k₀ l Z) ×
        DerivedCategory (ProEtaleWeilSheaf k₀ l Z))
      (DerivedCategory (ProEtaleWeilSheaf k₀ l U))).obj
        (((ObjectProperty.ι (NativeIsKFlat k₀ l Z)) ⋙ DerivedCategory.Q).prod
          ((ObjectProperty.ι (NativeIsKFlat k₀ l Z)) ⋙ DerivedCategory.Q))).FullyFaithful

/-- The native resolving-pair restriction is fully faithful.

Source: Stacks 06YS (lemma-K-flat-resolution) and lem-pur-derived-resolving-pair-restriction.
(blueprint: new-sf-native-open-tensor-pair-restriction-stage3)

Proof: every native complex K receives a quasi-isomorphism from a NativeIsKFlat complex:
transport K through the native ringed bridge, take a flat-term K-flat resolution there
(lem-pc-kflat-resolution) and transport back; the bridge carries the sheaf tensor to the
ringed tensor, so the resolution passes both quasi-isomorphism tests of NativeIsKFlat.
With this resolution property, derivedResolvingPairRestriction for the predicate
NativeIsKFlat on Z gives the fully faithful precomposition. -/
theorem nativePairRestrictionStage3 :
    Nonempty (NativePairRestrictionData k₀ l j) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
