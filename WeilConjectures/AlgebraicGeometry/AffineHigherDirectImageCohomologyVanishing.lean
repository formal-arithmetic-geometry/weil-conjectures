/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # The vanishing columns of Leray over an affine scheme

## References

* Stacks Project, Tags 01XJ, 01XB and 03FD
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Every positive cohomology group of a higher direct image vanishes on an affine base
(Stacks, Tags 01XJ, 01XB and 03FD). -/
theorem isZero_affine_higherDirectImage_moduleCohomology
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [IsAffine S]
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : M.IsQuasicoherent)
    (q p : ℕ) (hp : 0 < p) :
    IsZero ((RingedSpace.moduleCohomology S.toRingedSpace p).obj
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj M)) := by
  let N := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj M
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : M.IsQuasicoherent := hM
  let : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_higherDirectImage f M q
  obtain ⟨e, _⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison S p
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  let : Subsingleton (Scheme.Modules.H N (k + 1)) :=
    Scheme.Modules.subsingleton_H_succ_of_isAffine N k
  let : Subsingleton ((RingedSpace.moduleCohomology S.toRingedSpace (k + 1)).obj N) :=
    (e N).toEquiv.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry
