/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.AlgebraicGeometry.ConstructibleRestrictionClassCore

/-!
# Constructible representatives of restricted cohomology classes

Source: Stacks Project, Tags 03SA(3) and 03Q5.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A cohomology class in the restriction of a module sheaf comes from a constructible
module sheaf mapping to it. No injectivity or properness is needed.

Source: Stacks Project, Tags 03SA(3) and 03Q5. -/
theorem exists_constructible_restriction_class
    {X X₀ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X₀] [QuasiSeparatedSpace X₀] (i : X₀ ⟶ X)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (c : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj F)) q) :
    ∃ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Scheme.IsConstructibleEtaleModuleSheaf G ∧
      ∃ (a : G ⟶ F)
        (z : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
          AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj G)) q),
        Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
          AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1} Λ].map a)) q z = c := by
  classical
  obtain ⟨A, _, hA, D, hD, ι, hι⟩ :=
    Scheme.exists_filtered_colimit_constructible F
  obtain ⟨a, z, hz⟩ := exists_restriction_class_of_filtered_presentation
    (i := i) (Λ := Λ) ι hι q c
  exact ⟨D.obj a, hD a, ι.app a, z, hz⟩

end AlgebraicGeometry.Etale
