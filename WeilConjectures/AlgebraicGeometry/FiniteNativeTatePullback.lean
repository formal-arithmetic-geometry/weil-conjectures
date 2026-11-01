/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Root-induced native finite Tate pullback

Source: the root-adjunct calculation in Step 4 of
`lem-pur-finite-native-tate-source-comparison`, using Stacks 03PK.
(blueprint: def-pur-finite-native-tate-pullback)

## Main definitions

- `finiteNativeTateLine`: scalar extension of roots and its nonnegative tensor powers.
- `finiteNativeTateRootPull`: the free/forget and native inverse-image adjunct of roots.
- `finiteNativeTatePull`: its unit and monoidal extension to all powers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- The native heart line, in the internal coefficient presentation: scalar extension
of the additive roots, with the unit and positive tensor powers. This is the finite
formula of `sk-def-sp-tate-twist`, before passage to a single complex.
(blueprint: def-pur-finite-native-tate-pullback). -/
@[reducible] def finiteNativeTateLine (T : Scheme.{u}) (N : ℕ) : ℕ → Internal A T
  | 0 => 𝟙_ (Internal A T)
  | 1 => (Mod.freeFunctor (condensedRingObj (coefficient A) T)).obj
      (Scheme.proEtaleRootsOfUnitySheaf T N)
  | m + 2 => finiteNativeTateLine T N (m + 1) ⊗
      (Mod.freeFunctor (condensedRingObj (coefficient A) T)).obj
        (Scheme.proEtaleRootsOfUnitySheaf T N)

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
