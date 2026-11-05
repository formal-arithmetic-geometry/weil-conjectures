/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Reduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportDerived

/-!

# The reduction of a direct image is of étale origin

For a quasi-compact quasi-separated morphism `f : X ⟶ Y` and a bounded below complex `K` of
`𝒪_{E,X}`-modules whose first derived reduction `K ⊗ᴸ 𝔽_E` is of étale origin, the first derived
reduction of `Rf_* K` is of étale origin
(`ProEtale.CondensedRing.plusEtaleOrigin_derivedReduction_rightDerivedLowerStar_obj`): the
reduction commutes with `Rf_*` on bounded below complexes
(`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`,
`ProEtale.isIso_residueFieldDerivedPushHom`), and `Rf_*` preserves complexes of étale origin
(`ProEtale.DerivedCategory.plusEtaleOrigin_rightDerivedLowerStar_obj`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
  [QuasiCompact f] [QuasiSeparated f]

end AlgebraicGeometry.ProEtale.CondensedRing
