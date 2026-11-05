/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectGluingEndpointProperties
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Localized Mayer--Vietoris presentation of perfect objects

Source: Stacks Project, Tag 08BV
(blueprint: lem-perfect-gluing-triangle-presentation).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

noncomputable section

variable (Y : Scheme.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ W : Y.Opens,
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]

end

end AlgebraicGeometry.Scheme
