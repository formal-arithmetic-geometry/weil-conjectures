/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology
import WeilConjectures.AlgebraicGeometry.PositiveDirectImageOfObjectAcyclic

/-! # Positive direct-image vanishing

Source: Stacks Project, Tags 03DW, 03P2 and 0733.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- The positive derived direct images of a tensor-sections quasi-coherent sheaf
along the inclusion of opens vanish (Stacks, Tags 03P2, 03F3 and 072W). -/
theorem etaleTensorPositiveDirectImageVanishing
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology]
    [(i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    IsZero ((((i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).rightDerived (n + 1)).obj
      (etaleTensorSectionsSheaf F))) := by
  apply positiveDirectImageOfObjectAcyclic X i hi (etaleTensorSectionsSheaf F) n
  exact etaleTensorPositiveObjectCohomology X F n

end AlgebraicGeometry.Scheme.Modules
