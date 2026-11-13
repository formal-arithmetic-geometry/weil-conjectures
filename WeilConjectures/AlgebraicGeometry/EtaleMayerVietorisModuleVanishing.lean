/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisModuleExactSegment

/-! # Two-open Mayer--Vietoris vanishing for module sheaves

Source: Stacks Project, Tag 0A51, the Mayer--Vietoris induction, and Tag 03D3.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Vanishing in the adjacent terms of a two-open Mayer--Vietoris sequence.
Source: Stacks Project, Tags 0A50 and 0A51, the exact segment used in the induction. -/
theorem Etale.subsingleton_H_of_two_open_pullback_cover
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) (r : ℕ)
    (hU : Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst U.ι i)^*[ModuleCat.{u + 1} Λ].obj
          ((U.ι)^*[ModuleCat.{u + 1} Λ].obj J))) (r + 1)))
    (hV : Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst V.ι i)^*[ModuleCat.{u + 1} Λ].obj
          ((V.ι)^*[ModuleCat.{u + 1} Λ].obj J))) (r + 1)))
    (hI : Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst (U ⊓ V).ι i)^*[ModuleCat.{u + 1} Λ].obj
          (((U ⊓ V).ι)^*[ModuleCat.{u + 1} Λ].obj J))) r))
    : Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) (r + 1)) := by
  obtain ⟨δ, ρ, hexact⟩ :=
    Etale.exists_module_mayer_vietoris_exact_segment Λ i J U V hcover r
  have := hU
  have := hV
  have := hI
  let F := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
    ((i)^*[ModuleCat.{u + 1} Λ].obj J)
  have hzero : ∀ a : Sheaf.H F (r + 1), a = 0 := by
    intro a
    obtain ⟨c, hc⟩ := (hexact a).mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim c 0, map_zero] at hc
    exact hc.symm
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

end AlgebraicGeometry
