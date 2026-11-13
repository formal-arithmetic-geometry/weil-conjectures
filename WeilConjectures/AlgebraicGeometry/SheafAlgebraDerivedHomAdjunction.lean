/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.AlgebraicGeometry.SheafAlgebraMapDerivedAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The constructed algebra-valued derived Hom adjunction

## References

* [Stacks Project, Tag 0BV0](https://stacks.math.columbia.edu/tag/0BV0)
* [Stacks Project, Tag 0BV1](https://stacks.math.columbia.edu/tag/0BV1)
* [Stacks Project, Tag 0A6F](https://stacks.math.columbia.edu/tag/0A6F)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public section

universe u w wB

open CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry

/-- The explicit algebra-valued derived Hom is right adjoint to derived restriction
of scalars. No finiteness, Noetherianity, cohomological bound, or assertion about
quasi-coherence of the output is involved. -/
theorem sheafAlgebraDerivedHom_adjunction
    (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right))] :
    Nonempty ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).rightDerivedFunctor ⊣
          derivedRHomAlgebraModule Y B hB) := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).map B.hom)
  have : PreservesFiniteLimits F := sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  have : PreservesFiniteColimits F := sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  obtain ⟨adj⟩ := sheafAlgebra_mapDerivedCategory_adjunction Y B hB
  exact ⟨adj.ofNatIsoLeft F.rightDerivedFunctorIsoMapDerivedCategory.symm⟩

end AlgebraicGeometry
