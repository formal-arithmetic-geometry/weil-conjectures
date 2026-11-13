/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackQCoHLocal

/-! # Quasi-coherence of tensor pullback on ringed spaces

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace

/-- Tensor pullback along any morphism of ringed spaces preserves quasi-coherence. -/
theorem tensorModulePullback_isQuasicoherent
    {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (G : SheafOfModules.{u} (moduleRings Y)) (hG : G.IsQuasicoherent) :
    (SheafOfModules.changeOfRings.{u, u, u}
      (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
      (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf G)).IsQuasicoherent := by
  classical
  let M := SheafOfModules.changeOfRings.{u, u, u}
    (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
    (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf G)
  choose U hU hQU using fun x ↦ tensorModulePullback_isQuasicoherent_local g G hG x
  have hcov : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U hcov

end AlgebraicGeometry.RingedSpace
