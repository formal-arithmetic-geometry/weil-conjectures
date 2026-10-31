/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionBinary
import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionUnitPart
import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionAssociativityPart

/-!
# Unit and associativity laws from normalized binary composition
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Unit and associativity laws from normalized binary composition.
Source: Stacks Project, Tag 02V0.
-/
theorem locallyClosedModel_unit_associativity (G : LocallyClosedModelComposition.{u}) :
    ∃ identity : ∀ X : LocallyClosedCoefficients.{u},
        (LocallyClosedCoefficientImmersion.identity X).modelExtension ≅
          𝟭 (proEtaleRingModules X.scheme X.ring),
      (∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
        ∃ h : a.comp (.identity S) = a,
          G.gamma a (.identity S) ≪≫
              eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h) =
            Functor.isoWhiskerRight (identity S) a.modelExtension ≪≫
              Functor.leftUnitor a.modelExtension) ∧
      (∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
        ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
          G.gamma (.identity X) a ≪≫
              eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h) =
            Functor.isoWhiskerLeft a.modelExtension (identity X) ≪≫
              Functor.rightUnitor a.modelExtension) ∧
      (∀ {S X T W : LocallyClosedCoefficients.{u}}
        (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
        (d : LocallyClosedCoefficientImmersion W T),
        ∃ h : (a.comp b).comp d = a.comp (b.comp d),
          Functor.isoWhiskerRight (G.gamma b d) a.modelExtension ≪≫ G.gamma a (b.comp d) =
            Functor.associator d.modelExtension b.modelExtension a.modelExtension ≪≫
              Functor.isoWhiskerLeft d.modelExtension (G.gamma a b) ≪≫
                G.gamma (a.comp b) d ≪≫
                  eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h)) := by
  obtain ⟨identity, inner, outer⟩ := locallyClosedModel_unit_part G
  exact ⟨identity, inner, outer, locallyClosedModel_associativity_part G⟩
end AlgebraicGeometry.Scheme
