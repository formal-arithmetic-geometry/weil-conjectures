/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.KoszulOpenOrthogonality
import WeilConjectures.AlgebraicGeometry.AffineDerivedOpenTransport
import WeilConjectures.AlgebraicGeometry.AffineKoszulGeometricProperties
import Mathlib.Topology.Compactness.Bases
import Mathlib.Data.Fintype.EquivFin
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Affine Koszul construction with its open restriction unit
Source: Stacks Project, Tags 0A9A and 09IR.
(blueprint: lem-pc-supported-perfect-detector-affine-construction).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Kernel and cokernel closure give quasi-coherent homology, then descend through Q. -/
private theorem qcoh_of_qcoh_terms (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (L : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hL : ∀ n, (L.X n).IsQuasicoherent) :
    schemeDerivedQCohProperty Y (DerivedCategory.Q.obj L) := by
  intro n
  let S := L.sc n
  have : S.X₁.IsQuasicoherent := hL _
  have : S.X₂.IsQuasicoherent := hL _
  have : S.X₃.IsQuasicoherent := hL _
  have := Scheme.Modules.isQuasicoherent_kernel S.g
  have hq := Scheme.Modules.isQuasicoherent_cokernel (kernel.lift S.g S.f S.zero)
  exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
    ((S.homologyIsoCokernelLift).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).app L).symm) hq

end AlgebraicGeometry
