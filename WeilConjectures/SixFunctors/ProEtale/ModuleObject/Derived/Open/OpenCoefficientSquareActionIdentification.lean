/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ExtensionIsoQuotientFormula
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! # The identity action normalization of the open coefficient square

The auxiliary constructions retain the specified balanced collapse and build the reverse
comparison from restriction along the inverse coefficient maps. No coefficient flatness is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X)

/-- Pullback written using restriction along the inverse coefficient isomorphism. -/
noncomputable def openCoefficientRestriction :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U) :=
  (ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ X) ⋙
    Mod.comap (asIso (condensedPullbackHom Λ j)).inv

/-- The specified extension-to-inverse-restriction collapse, natural in the module. -/
noncomputable def openCoefficientCollapse :
    upperStar Λ j ≅ openCoefficientRestriction Λ j :=
  Functor.isoWhiskerLeft ((ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ X))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j))

variable {Λ}
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

end AlgebraicGeometry.ProEtale.CondensedRing
