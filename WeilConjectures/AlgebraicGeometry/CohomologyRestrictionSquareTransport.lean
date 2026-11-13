/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.CohomologyModuleSquareCompatibility

/-!
# Transport of a cohomology square through bijective restriction maps

Source: the restriction-map calculation in Stacks Project, proof of Tag 095T,
and functoriality of inverse image and Ext pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- A commuting square whose vertical restrictions are bijective identifies its
total-space cohomology map with its restricted cohomology map.

Source: Stacks Project, proof of Tag 095T, the final stalk-map calculation;
Tag 03FD for the underlying abelian coefficient convention. -/
theorem Etale.exists_addEquiv_cohomology_restrictionSquare
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' X₀ X₀' : Scheme.{u}} (g : X' ⟶ X) (i : X₀ ⟶ X)
    (j : X₀' ⟶ X') (k : X₀' ⟶ X₀) (h : j ≫ g = k ≫ i)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (hi : Function.Bijective (Etale.cohomologyMap i
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q))
    (hj : Function.Bijective (Etale.cohomologyMap j
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((g)^*[ModuleCat.{u + 1} Λ].obj F)) q)) :
    ∃ (b₁ : Sheaf.H
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q ≃+
        Sheaf.H
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (b₂ : Sheaf.H ((g)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q ≃+
        Sheaf.H ((k)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, b₂ (Etale.cohomologyMap g
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q x) =
        Etale.cohomologyMap k
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} Λ].obj F)) q (b₁ x) := by
  obtain ⟨c₁, c₂, c₃, hc⟩ :=
    Etale.exists_addEquiv_cohomology_moduleSquare Λ g i j k h F q
  let r₁ := AddEquiv.ofBijective (Etale.cohomologyMap i
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) hi
  let r₂ := AddEquiv.ofBijective (Etale.cohomologyMap j
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((g)^*[ModuleCat.{u + 1} Λ].obj F)) q) hj
  exact ⟨r₁.trans c₁, (c₂.trans r₂).trans c₃, hc⟩

end AlgebraicGeometry
