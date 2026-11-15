/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
import WeilConjectures.AlgebraicGeometry.ProjTwistTransportedData
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineTwist

/-!
# Comparing a Proj twist with a prescribed glued twist

## References

* Stacks Project, Constructions: Tags 01MN and 01M7.
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For a fixed chart-compatible comparison, every module with the prescribed
standard generators pulls back to the corresponding Proj twist. -/
theorem nonempty_twist_iso_tensorPullback_of_twistData (k : Type v) [Field k]
    (d : ℤ) (C : ProjectiveLine.ProjChartIsomorphism k)
    (L : (ProjectiveLine (Spec (.of k))).Modules)
    (T : ProjectiveLine.TwistData (Spec (.of k)) d L) :
    Nonempty (twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d ≅
      (Scheme.Modules.tensorPullback C.iso.hom).obj L) := by
  classical
  let M := twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d
  let N := (Scheme.Modules.pullback C.iso.inv).obj M
  obtain ⟨TN⟩ := nonempty_twistData_pullback_inv k d C
  let T₀ := ProjectiveLine.twistData (Spec (.of k)) d
  obtain ⟨eN, _, _⟩ := T₀.existsUnique_iso TN
  obtain ⟨eL, _, _⟩ := T₀.existsUnique_iso T
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction C.iso.inv
  let epb := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction C.iso.inv)
  let e : (Scheme.Modules.tensorPullback C.iso.inv).obj M ≅ L :=
    epb.app M ≪≫ eN.symm ≪≫ eL
  obtain ⟨ecomp⟩ := Scheme.Modules.nonempty_tensorPullbackComp C.iso.hom C.iso.inv
  obtain ⟨eid⟩ := Scheme.Modules.nonempty_tensorPullbackId
    (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k))
  have einv : (Scheme.Modules.tensorPullback C.iso.hom).obj
      ((Scheme.Modules.tensorPullback C.iso.inv).obj M) ≅ M := by
    have ec := ecomp.symm.app M
    rw [C.iso.hom_inv_id] at ec
    exact ec ≪≫ eid.app M
  exact ⟨einv.symm ≪≫ (Scheme.Modules.tensorPullback C.iso.hom).mapIso e⟩

end AlgebraicGeometry.Proj
