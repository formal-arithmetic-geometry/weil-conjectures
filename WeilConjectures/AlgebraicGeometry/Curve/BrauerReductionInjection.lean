/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsEpi
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Brauer pullback to the reduction of a curve
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- Pullback to the reduction is injective on the cohomological Brauer group of a curve. -/
theorem injective_brauer_pullback_reduction {k : Type u} [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] :
    Function.Injective (fun x : C.CohomologicalBrauerGroup ↦
      Sheaf.H.map (Scheme.upperStarGmSheafToGmSheaf C.nilradical.subschemeι) 2
        (Etale.cohomologyMap C.nilradical.subschemeι C.gmSheaf 2 x)) := by
  let i := C.nilradical.subschemeι
  let φ := Scheme.upperStarGmSheafToGmSheaf i
  have : Surjective i :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism C).2.2.1
  have : IsUniversalHomeomorphism i := {}
  have : Epi φ := Scheme.epi_upperStarGmSheafToGmSheaf_reduction C
  have : Subsingleton (Sheaf.H (Limits.kernel φ) 2) :=
    subsingleton_H_two_reduction_units_kernel f
  let S := ShortComplex.mk (Limits.kernel.ι φ) φ (Limits.kernel.condition φ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel φ }
  have hinj : Function.Injective (Sheaf.H.map φ 2) := by
    apply (injective_iff_map_eq_zero (Sheaf.H.map φ 2)).mpr
    intro x hx
    obtain ⟨y, hy⟩ := (Sheaf.H.exact_map_map hS 2 x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]
  exact hinj.comp (Etale.cohomologyMap_bijective i C.gmSheaf 2).1

end AlgebraicGeometry.IsCurve
