/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.ZariskiEtalePushedResolutionFiniteLimits
import WeilConjectures.AlgebraicGeometry.ZariskiEtalePushedResolutionQuasiIso

/-! # Injective resolutions for the Zariski-etale comparison

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 09AX](https://stacks.math.columbia.edu/tag/09AX)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- Local vanishing makes the direct image of an injective resolution a resolution. -/
theorem zariski_etale_pushed_resolution
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hvan : ∀ q : ℕ, 0 < q →
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        (0 : i.op ⋙ Sheaf.cohomologyPresheaf F q ⟶
          i.op ⋙ Sheaf.cohomologyPresheaf F q)) :
    PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) ∧
    ∀ (I : InjectiveResolution F),
      QuasiIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)
          (ComplexShape.up ℕ) 0).inv.app F ≫
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
              (ComplexShape.up ℕ)).map I.ι) := by
  constructor
  · exact zariski_etale_pushed_resolution_finite_limits i hi_inclusion hi
  · exact zariski_etale_pushed_resolution_quasi_iso i hi_inclusion hi F hvan
