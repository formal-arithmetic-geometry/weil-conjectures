/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.FlatModuleCanonicalDerivedPullbackAux
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleTensorFlat

/-! # The canonical derived pullback comparison at a flat module

## References

* Stacks Project, Tags 06YD and 06YJ
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- A canonical derived-to-ordinary pullback comparison at a quasi-coherent module
flat over its own scheme is invertible. The affine-local IsFlatOver predicate at the
identity expresses intrinsic flatness, independently of any family morphism
(Stacks, Tags 06YD and 06YJ). -/
theorem isIso_modulePullbackComparison_of_isFlatOver_identity
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G (𝟙 Y))
    (c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback a).obj G))
    (hc : IsDerivedModulePullbackComparison a G c) : IsIso c := by
  obtain ⟨ε, hε, hc⟩ := hc
  rw [hc]
  have := isIso_flat_single_derived_counit a G
    (isFlat_of_isFlatOver_identity G hflat) ε hε
  change IsIso (ε.app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback a) (ComplexShape.up ℤ) 0).hom.app G)))
  infer_instance

end AlgebraicGeometry
