/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.Compactification.Defs

/-! # The projective line is a genus-zero smooth proper connected curve

## References

* Stacks Project, Tag 0B2P (projective space is smooth) and Tag 0C6U (the projective line).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- The base-change projective line is a smooth proper connected curve, has genus zero,
and has vanishing first cohomology of its structure sheaf (Stacks, Tags 0B2P, 0C6U). -/
theorem isConnectedCurve_smooth_proper_genus_zero (k : Type u) [Field k] [IsAlgClosed k] :
    IsConnectedCurve (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)) ∧
    Smooth (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)) ∧
    IsProper (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)) ∧
    (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)).genus = 0 ∧
    Subsingleton ((RingedSpace.moduleCohomology
      (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k))).toRingedSpace 1).obj
      (Scheme.Modules.unit (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k))))) := by
  have hs : SmoothOfRelativeDimension 1
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := inferInstance
  have hdim : topologicalKrullDim (ProjectiveLine (Spec (.of k))) = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) 1
  have hc : IsConnectedCurve (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
    { krullDim_le_one := hdim.le
      connectedSpace := inferInstance
      krullDim_eq_one := hdim }
  refine ⟨hc, SmoothOfRelativeDimension.smooth 1 _, inferInstance, ?_, ?_⟩
  · obtain ⟨e⟩ := ProjectiveLine.nonempty_relativeDifferentials_iso_twist k
    have : Subsingleton ((twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).H 0) :=
      ProjectiveLine.subsingleton_H_zero_twist_of_neg k (-2) (by decide)
    have : Subsingleton
        ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials.H 0) :=
      Scheme.Modules.subsingleton_H_of_iso e.symm 0
    rw [Scheme.Hom.genus_eq_finrankH_zero, Scheme.Modules.finrankH]
    exact Module.finrank_zero_of_subsingleton
  · have : Subsingleton ((twist (ULift.{u} (Fin 2)) (Spec (.of k)) 0).H 1) :=
      ProjectiveLine.subsingleton_H_one_twist k 0 (by decide)
    have : Subsingleton ((Scheme.Modules.unit (ProjectiveLine (Spec (.of k)))).H 1) :=
      Scheme.Modules.subsingleton_H_of_iso
        (unitIsoTwistZero (ULift.{u} (Fin 2)) (Spec (.of k))).symm 1
    obtain ⟨e, _⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison
      (ProjectiveLine (Spec (.of k))) 1
    exact (e _).toEquiv.subsingleton

end AlgebraicGeometry.ProjectiveSpace
