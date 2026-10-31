/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImageSupplement
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

/-- Extend the projection pullback of roots by the free-module adjunction, then take
its adjunct under the native module inverse-image/direct-image adjunction. The sheaf
map into the target free module is the free/forget unit, so scalars are unchanged.
Source: Step 4 of the finite native source comparison; Stacks 03PK.
(blueprint: def-pur-finite-native-tate-pullback). -/
def finiteNativeTateRootPull {S T : Scheme.{u}} (h : S ⟶ T) (N : ℕ) :
    (CondensedRing.upperStar (coefficient A) h).obj (finiteNativeTateLine A T N 1) ⟶
      finiteNativeTateLine A S N 1 :=
  ((CondensedRing.upperStarLowerStarAdjunction (coefficient A) h).homEquiv _ _).symm
    (((Mod.freeForgetAdjunction (condensedRingObj (coefficient A) T)).homEquiv _ _).symm
      (Scheme.proEtaleRootsOfUnityDirectImageMap h N ≫
        (ProEtale.lowerStar Ab.{u + 1} h).map
          ((Mod.freeForgetAdjunction (condensedRingObj (coefficient A) S)).unit.app
            (Scheme.proEtaleRootsOfUnitySheaf S N))))

/-- Canonical native line pullback: the inverse monoidal unit map in degree zero,
the root adjunct in degree one, and inverse tensorator followed by tensor powers
in higher degrees. This construction does not use any coefficient encoding or line
comparison, and requires no choice of a root frame.
Source: Steps 3--4 of the finite native source comparison.
(blueprint: def-pur-finite-native-tate-pullback). -/
def finiteNativeTatePull {S T : Scheme.{u}} (h : S ⟶ T) (N : ℕ) :
    (m : ℕ) → (CondensedRing.upperStar (coefficient A) h).obj
      (finiteNativeTateLine A T N m) ⟶ finiteNativeTateLine A S N m
  | 0 => (Functor.Monoidal.εIso (CondensedRing.upperStar (coefficient A) h)).inv
  | 1 => finiteNativeTateRootPull A h N
  | m + 2 => (Functor.Monoidal.μIso (CondensedRing.upperStar (coefficient A) h)
      (finiteNativeTateLine A T N (m + 1)) (finiteNativeTateLine A T N 1)).inv ≫
        tensorHom (finiteNativeTatePull h N (m + 1)) (finiteNativeTateRootPull A h N)

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
