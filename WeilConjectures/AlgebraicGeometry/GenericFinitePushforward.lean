/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.GenericFiniteSourceLisse
import WeilConjectures.AlgebraicGeometry.GenericFiniteLissePreservation
import WeilConjectures.AlgebraicGeometry.PullbackFiniteLocallyConstant

/-!
# Generic lissity of finite direct images

## Implementation details

Finiteness of a sheaf here means finite geometric stalks, rather than finitely generated
abelian stalks.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite direct image of a constructible abelian etale sheaf is lisse on a dense
open of an integral Noetherian affine base. -/
theorem exists_dense_open_lisse_finite_directImage
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
    {Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g]
    (E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsConstructibleEtaleSheafOfSets
      ((sheafCompose Z.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      IsLisseEtaleSheafOfSets
        ((etaleSetPullback U.ι).obj
          ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((Etale.lowerStar AddCommGrpCat.{u + 1} g).obj E))) := by
  obtain ⟨U, hUd, hU⟩ := exists_dense_open_lisse_finite_source S g E hE
  obtain ⟨V, hVd, hV⟩ := exists_dense_open_finite_lisse_preservation S g
  refine ⟨U ⊓ V, ?_, ?_⟩
  · exact hUd.inter_of_isOpen_left hVd U.isOpen
  · have hWU : g ⁻¹ᵁ (U ⊓ V) ≤ g ⁻¹ᵁ U := fun x hx ↦ hx.1
    have hW := (pullback_finite_locally_constant
      (Z.homOfLE hWU) (g ⁻¹ᵁ U).ι E hU).2
    rw [Scheme.homOfLE_ι] at hW
    exact hV (U ⊓ V) inf_le_right E hW

end AlgebraicGeometry.Scheme
