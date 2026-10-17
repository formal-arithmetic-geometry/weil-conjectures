/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField

/-!
# Cohomology with supports and the exceptional inverse image of a closed immersion

For a closed immersion `i : Z ⟶ X` the cohomology with supports `H^a_Z(X, K)` of
`AlgebraicGeometry.Etale.derivedSupportCohomology` is `Hom(Λ_Z, Ri^!(K[a]))`
(`AlgebraicGeometry.Etale.supportCohomologyAddEquiv`): by `H^a_Z(X, K) ≅ Hom(i_* Λ_Z, K[a])`
(`AlgebraicGeometry.Etale.derivedSupportCohomologyAddEquiv`), `i_* Λ_Z ≅ Ri_! Λ_Z` and the
adjunction `Ri_! ⊣ Ri^!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section SupportHom

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- `Ri_! Λ_Z ≅ i_* Λ_Z`, placed in degree zero, for a closed immersion `i`. -/
noncomputable def rightDerivedLowerShriekConstantComplexIso :
    (R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))) :=
  (rightDerivedLowerShriekIsoRightDerivedLowerStar _ i).app _ ≪≫
    (rightDerivedFunctorLowerStarIsoMapDerivedCategory _ i).app _ ≪≫
    ((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.mapIso (constantComplexIsoSingleFunctor Λ Z) ≪≫
    (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _

/-- Blueprint `lem-pur-gysin-structure`: Structure of the exceptional inverse image of the zero
section (the identification of cohomology with supports with morphisms into `Ri^!`).

For a closed immersion `i : Z ⟶ X`, the cohomology with supports is
`H^a_Z(X, K) ≅ Hom(Λ_Z, Ri^!(K[a]))`. -/
noncomputable def supportCohomologyAddEquiv
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj K ≃+
      (constantComplex Λ Z ⟶ (R(i)^![ModuleCat.{u + 1} Λ]).obj (K⟦a⟧)) :=
  (derivedSupportCohomologyAddEquiv Λ i K a).trans
    ((AddEquiv.mk ((rightDerivedLowerShriekConstantComplexIso Λ i).homCongr
      (Iso.refl (K⟦a⟧))).symm (fun f g ↦ by simp [Iso.homCongr])).trans
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).homAddEquiv _ _))

end SupportHom

end Etale

end AlgebraicGeometry
