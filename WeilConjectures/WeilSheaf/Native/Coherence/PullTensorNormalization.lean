/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativePullTensor

/-!
# The normalization of the native pullback–tensor comparison

`nativePullTensor` is, by definition, the descent `nativeRestrictionDerivedTensor` of
`nativePullTotalTensor` along the pullback `upperStar`; its normalization on native K-flat
representatives is the specialization of the normalization of that descent,
`NativeRestrictionDescentProof.restrictionDerivedOfTotal_normalization`.

The instances are resolved as in the file defining `nativeOpenPull` (no priority change on the
Grothendieck instance of the coefficient modules), and the fixed arguments of the normalization
predicate are inferred from the proof, so that the kernel compares `nativePullTensor` with its
definition syntactically.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]

set_option diagnostics true in
/-- The descent `nativeRestrictionDerivedTensor` is normalized on native K-flat representatives
by the total comparison it descends. -/
theorem nativeRestrictionDerivedTensor_normalization
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) :
    OpenTensorRestrictionNormalization R
      (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
      (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
      (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
      (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
      (NativeRestrictionDescentProof.totalFamily R
        (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y) t)
      (nativeRestrictionDerivedTensor k₀ l R hR t) :=
  have := native_open_tensor_full_kflat_localization k₀ l Y
  NativeRestrictionDescentProof.restrictionDerivedOfTotal_normalization R
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
    (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
    (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
    (nativeOpenTensorModel_naturality k₀ l Z) (nativeOpenTensorModel_naturality k₀ l Y) t

variable (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

-- The identification of `nativePullTensor` with its definition is a kernel conversion between
-- instance terms elaborated in different files (build logs C5-20261105T05*); budget raised.
set_option maxHeartbeats 1600000 in
set_option diagnostics true in
/-- On native K-flat representatives, `nativePullTensor` is the localization of
`nativePullTotalTensor` under the models `nativeOpenTensorModel`. -/
theorem nativePullTensor_normalization :
    OpenTensorRestrictionNormalization (upperStar k₀ l g)
      (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
      (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
      (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y)
      (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g)
      (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
      (NativeRestrictionDescentProof.totalFamily (upperStar k₀ l g)
        (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y) (nativePullTotalTensor k₀ l g))
      (nativePullTensor k₀ l g) :=
  nativeRestrictionDerivedTensor_normalization k₀ l (upperStar k₀ l g)
    (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g) (nativePullTotalTensor k₀ l g)

end AlgebraicGeometry.ProEtaleWeilSheaf
