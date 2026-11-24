/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.GenericFiniteSchemeSplitting
import WeilConjectures.AlgebraicGeometry.FiniteSplitCoverLisseImage
import WeilConjectures.AlgebraicGeometry.LisseEtaleSurjectiveDescent

/-!
# A generic locus where a finite map preserves lissity
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- There is a dense open depending only on a finite morphism, over every open of
which its direct image preserves finite local constancy. No constructibility of `E`
is assumed: only its restriction to the inverse image of `V` needs to be lisse. -/
theorem exists_dense_open_finite_lisse_preservation
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
    {Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g] :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      ∀ (V : S.Opens), V ≤ U →
        ∀ (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}),
          IsLisseEtaleSheafOfSets
            ((sheafCompose (g ⁻¹ᵁ V).toScheme.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
                ((Etale.upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ V).ι).obj E)) →
          IsLisseEtaleSheafOfSets
            ((etaleSetPullback V.ι).obj
              ((sheafCompose S.smallEtaleTopology
                (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
                  ((Etale.lowerStar AddCommGrpCat.{u + 1} g).obj E))) := by
  obtain ⟨U, hUd, hU⟩ := exists_dense_open_finite_scheme_splitting S g
  refine ⟨U, hUd, ?_⟩
  intro V hVU E hE
  obtain ⟨T, p, _, hpEtale, hpSurj, n, W, hcover, hdisjoint, hW⟩ := hU V hVU
  let : Etale p := hpEtale
  let : Surjective p := hpSurj
  apply isLisseEtaleSheafOfSets_of_etale_surjective_pullback p
  exact isLisse_pullback_finite_directImage_of_split_cover g V p n W
    hcover hdisjoint hW E hE

end AlgebraicGeometry.Scheme
