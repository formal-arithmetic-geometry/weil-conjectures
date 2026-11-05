/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativePullTensor

/-!
# Normalization of the native restriction–tensor comparisons

For an exact functor `R` between pro-étale Weil sheaves preserving native K-flatness and a
comparison `t` of native total tensor complexes along `R`, the derived comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeRestrictionDerivedTensor` is, on native K-flat
representatives, the localization of `t`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeRestrictionDerivedTensor_normalization`). In particular
this describes the native pullback–tensor comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTensor`.

The functor `R` is kept abstract, so that the statement can be instantiated with a concrete
pullback functor without the kernel unfolding it.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

-- Use Mathlib's Grothendieck instance on module categories, as the native tensor files do.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]

attribute [local irreducible] nativeTensorTotal nativeDerivedTensor NativeIsKFlat
  nativeOpenTensorModel nativeOpenTensorInsertion

/-- On native K-flat representatives `P`, `T`, the derived comparison
`nativeRestrictionDerivedTensor k₀ l R hR t` is the localization of the total comparison `t`,
under the native K-flat models `nativeOpenTensorModel`. -/
theorem nativeRestrictionDerivedTensor_normalization
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) :
    OpenTensorRestrictionNormalization R (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
      (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
      (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
      (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
      (fun P T ↦ t.app (P, T)) (nativeRestrictionDerivedTensor k₀ l R hR t) :=
  have := native_open_tensor_full_kflat_localization k₀ l Y
  NativeRestrictionDescentProof.restrictionDerivedOfTotal_normalization R
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
    (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
    (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
    (nativeOpenTensorModel_naturality k₀ l Z) (nativeOpenTensorModel_naturality k₀ l Y) t

end AlgebraicGeometry.ProEtaleWeilSheaf
