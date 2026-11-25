/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenSheafTensorExistence
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorLocalization
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalization

/-! # Native open derived tensor and balanced pullback composition

For an open immersion `j : U ⟶ Z`, this file constructs the native comparisons between the
derived tensor product and the extension/restriction functors along `j`.

All functors act on the ambient derived categories of actual pro-étale Weil
module sheaves. The record retains sheaf, total-complex and derived normalization.
The ordinary inverse is pinned by the open unit, as in openTensorNormalization.

## Main definitions

* `NativeOpenTensorData`: equivariant sheaf comparison and K-flat preservation.
* `OpenTensorPresentation`: total-complex and localization normalization.
* `NativeOpenDerivedTensorData`: natural derived comparison and forgetting square.
* `nativeOpenPullComp`: localization of the canonical balanced compositor.

## Main statements

* `native_open_derived_tensor`: existence of the normalized native comparisons.

## Implementation details

The sheaf-level comparison sends `[x] ⊗ y` to `[x ⊗ y|U]`; its inverse is the open-unit
transpose. Applied in each bidegree it gives a chain isomorphism of total tensor complexes, which
shows that extension and restriction preserve K-flatness. Localizing the natural chain map and its
inverse gives the derived comparison, independently of the chosen resolutions. No lisse,
boundedness or degree-zero hypothesis is used.

## References

* [Stacks Project, Tags 0GL1, 0E8I and 03D8](https://stacks.math.columbia.edu)
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

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

/-- The equivariant open tensor theorem, on arbitrary unbounded ambient inputs: there exist native
open tensor data, a derived tensor comparison and a total-complex presentation that are
compatible. -/
theorem native_open_derived_tensor :
    ∃ (s : NativeOpenTensorData k₀ l j) (d : NativeOpenDerivedTensorData k₀ l j s)
      (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z)),
      NativeOpenPresentationCompatibility k₀ l j s d c := by
  obtain ⟨adj, sheafRestriction, sheafGamma, hu, hcounit, hr, hi, hE, hR⟩ :=
    native_open_sheaf_tensor_existence k₀ l j
  have hunit (M : ProEtaleWeilSheaf k₀ l U) : IsIso (adj.unit.app M) := by
    let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U)
    have : IsIso (F.map (adj.unit.app M)) := by
      change IsIso ((adj.unit.app M).hom.f)
      rw [hu M]
      infer_instance
    exact isIso_of_reflects_iso (adj.unit.app M) F
  let s : NativeOpenTensorData k₀ l j :=
    { adj := adj
      unit_forget := hu
      counit_forget := hcounit
      unit_iso := hunit
      sheafRestriction := sheafRestriction
      restriction_forget := hr
      sheafGamma := sheafGamma
      sheaf_inverse := hi
      extension_kflat := hE
      restriction_kflat := hR }
  obtain ⟨rho, gamma, c, hc⟩ := native_open_tensor_localization k₀ l j s
  obtain ⟨hunit, hord⟩ := native_open_tensor_normalization k₀ l j s rho gamma c hc
  refine ⟨s, ⟨gamma, rho, hunit, hord⟩, c, ?_⟩
  exact hc

end AlgebraicGeometry.ProEtaleWeilSheaf
