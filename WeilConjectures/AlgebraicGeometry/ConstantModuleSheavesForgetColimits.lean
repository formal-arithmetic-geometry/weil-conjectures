/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Forgetting constant module coefficients preserves colimits

Source: Stacks Project, Tags 03DB and 03CO.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Forgetting constant module coefficients preserves colimits of the size of the
coefficient category, on any small etale site.
Source: Stacks Project, Tag 03DB, proof of lemma-limits-colimits; Tag 03CO,
lemma-limits-colimits-abelian-sheaves. -/
theorem constantModuleSheaves_forget_preservesColimits (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  let f : ℤ →+* Λ := Int.castRingHom Λ
  let U := ModuleCat.restrictScalars.{u + 1} f
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} f).isLeftAdjoint
  have : (U ⋙ V).IsLeftAdjoint := inferInstance
  have : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    inferInstanceAs (U ⋙ V).IsLeftAdjoint
  let J := X.smallEtaleTopology
  let G := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
    Functor.isoWhiskerLeft (sheafCompose J G)
      (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm ≪≫
      Functor.rightUnitor (sheafCompose J G)
  have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
  have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
  infer_instance

end AlgebraicGeometry.Etale
