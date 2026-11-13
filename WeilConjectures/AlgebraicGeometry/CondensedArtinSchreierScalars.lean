/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarFromPointAdditive
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear

/-! # The condensed character projector as a linear average -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

-- Explicit monoidal module comparisons need additional elaboration heartbeats.
private theorem linear_lowerStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint X) (R := Λ))
    let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint Y) (R := Λ))
    (CondensedRing.lowerStar Λ f).Linear (MonObj.Γ Λ) := by
  dsimp only
  apply Mod.linear_mapMod_comp_comap
    (R := condensedRingObj Λ X) (S := condensedRingObj Λ Y)
    (lowerStar Ab.{u + 1} f) (condensedPushforwardHom Λ f)
    (MonObj.Γ.mapFunctor (upperStarFromPoint X))
    (MonObj.Γ.mapFunctor (upperStarFromPoint Y))
  intro a
  simp only [MonObj.Γ.mapFunctor_hom, condensedPushforwardHom,
    Adjunction.unitAlgHom, Category.assoc]
  exact (upperStarLowerStarAdjunction Ab.{u + 1} f).ε_comp_map_comp_unit_app_comp_map
    (upperStarFromPoint Y) (upperStarFromPoint X) (upperStarFromPointComp f).hom a.hom

-- Explicit monoidal module comparisons need additional elaboration heartbeats.
/-- Module pullback is linear for scalars pulled back from the coefficient point.
Source: the linear module adjunction. -/
theorem condensedModulePullback_linear
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint X) (R := Λ))
    let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint Y) (R := Λ))
    (CondensedRing.upperStar Λ f).Linear (MonObj.Γ Λ) := by
  dsimp only
  let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint X) (R := Λ))
  let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint Y) (R := Λ))
  let := linear_lowerStar Λ f
  exact (CondensedRing.upperStarLowerStarAdjunction Λ f).left_adjoint_linear

-- Explicit monoidal module comparisons need additional elaboration heartbeats.
private theorem regularEnd_eq_smul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (a : MonObj.Γ Λ) :
    let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint X) (R := Λ))
    (Mod.regularEndRingHom (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint X) a)).asHom =
      a • 𝟙 (Mod.regular (condensedRingObj Λ X)) := by
  exact Mod.regularEndRingHom_eq_smul
      (MonObj.Γ.mapFunctor (upperStarFromPoint X) (R := Λ)) a

-- Explicit monoidal module comparisons need additional elaboration heartbeats.
/-- In the linear structure induced from the coefficient ring, the defining condensed
projector is the usual normalized sum of its translation endomorphisms.

Source: latest blueprint, `def-fd-artin-schreier-sheaf.md`, displayed projector, and
`prop-kernel-lisse.proof.md`, the character average. -/
theorem condensedArtinSchreierProjector_eq_sum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    [Invertible (Fintype.card k : MonObj.Γ Λ)] (ψ : AddChar k (MonObj.Γ Λ)) :
    let := Mod.linearOfRingHom
      (MonObj.Γ.mapFunctor (upperStarFromPoint (AffineSpace PUnit (Spec (.of k))))
        (R := Λ))
    condensedArtinSchreierProjector Λ k ψ =
      ∑ a : k, (⅟(Fintype.card k : MonObj.Γ Λ) * ψ (-a)) •
        condensedArtinSchreierTranslationAction Λ k a := by
  classical
  dsimp only
  let A : Scheme.{u} := AffineSpace PUnit.{u + 1} (Spec (.of k))
  let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint A) (R := Λ))
  let := linear_lowerStar Λ
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))
  unfold condensedArtinSchreierProjector
  simp only [condensedArtinSchreierPushforward] at *
  apply Finset.sum_congr rfl
  intro a _
  apply End.ext
  simp only [End.smul_asHom]
  rw [regularEnd_eq_smul, Functor.map_smul, CategoryTheory.Functor.map_id,
    Linear.comp_smul]
  erw [Category.comp_id]
  congr 2
  exact Ring.inverse_invertible _

end AlgebraicGeometry.ProEtale
