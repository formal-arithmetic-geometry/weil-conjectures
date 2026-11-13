/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenFiniteComplement
import WeilConjectures.AlgebraicGeometry.Curve.GmFiniteModificationOpenIso
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport

/-! # Brauer pullback along finite modifications of reduced curves
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- A finite morphism which is an isomorphism over a dense open of a reduced curve
induces an injection on its cohomological Brauer group. -/
theorem injective_brauer_pullback_finite_modification {k : Type u} [Field k]
    [IsAlgClosed k] {C Y : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsReduced C] (ν : Y ⟶ C) [IsFinite ν] (V : C.Opens) (hV : Dense (V : Set C))
    [IsIso (ν ∣_ V)] :
    Function.Injective (fun x : C.CohomologicalBrauerGroup ↦
      Sheaf.H.map (Scheme.upperStarGmSheafToGmSheaf ν) 2
        (Etale.cohomologyMap ν C.gmSheaf 2 x)) := by
  obtain ⟨hfin, hcl, hsep⟩ := dense_open_finite_complement f V hV
  have hφ := Scheme.isIso_upperStar_map_gmSheafToLowerStar_of_isIso_restrict ν V
  have hinj := (Etale.bijective_H_map_of_isIso_upperStar_map V hfin hcl hsep
    (Scheme.gmSheafToLowerStarGmSheaf ν) hφ 0).injective
  have hedge := (Etale.bijective_edgeMap_of_isFinite ν Y.gmSheaf 2).injective
  have hcomp := hedge.comp hinj
  convert hcomp using 1
  funext x
  dsimp only [Function.comp_apply]
  rw [Etale.cohomologyMap_map, Scheme.upperStarGmSheafToGmSheaf,
    Adjunction.homEquiv_counit, Sheaf.H.map_comp_apply]
  rfl

end AlgebraicGeometry.IsCurve
