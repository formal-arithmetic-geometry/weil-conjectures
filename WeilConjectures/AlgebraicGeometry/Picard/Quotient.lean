/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Group

/-!
# The relative Picard functor as a quotient presheaf

For a morphism of schemes `f : X ⟶ S`, the quotient presheaf `T ↦ Pic(X_T) / f_T^* Pic(T)` on
schemes over `S` (`AlgebraicGeometry.picardQuotientPresheaf`): the relative Picard functor
`Pic_{X/S}` (`AlgebraicGeometry.picardFunctor`) is its fppf sheafification. The classes pulled
back from the base form the subgroup `AlgebraicGeometry.picardBaseClasses f T`, and the base
change maps of the Picard presheaf descend to the quotients because pulling back along
`X_{T'} ⟶ X_T` and then along `f_{T'}` is pulling back along `f_T` and then along `T' ⟶ T`
(`AlgebraicGeometry.isPullback_baseChangeMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}}

/-- The subgroup `f_T^* Pic(T)` of `Pic(X_T)`: the classes pulled back from the base `T`. -/
noncomputable abbrev picardBaseClasses (f : X ⟶ S) (T : Over S) :
    Subgroup (pullback f T.hom).Pic :=
  (Pic.mapHom (pullback.snd f T.hom)).range

/-- Pulling back along `X_{T'} ⟶ X_T` sends classes from `T` to classes from `T'`. -/
lemma picardBaseClasses_le_comap (f : X ⟶ S) {T T' : Over S} (φ : T' ⟶ T) :
    picardBaseClasses f T ≤ (picardBaseClasses f T').comap (Pic.mapHom (baseChangeMap f φ)) := by
  rintro _ ⟨N, rfl⟩
  rw [Subgroup.mem_comap, MonoidHom.mem_range]
  refine ⟨Pic.map φ.left N, ?_⟩
  simp only [Pic.mapHom_apply]
  rw [← Pic.map_comp, ← Pic.map_comp, (isPullback_baseChangeMap f φ).w]

/-- The quotient presheaf `T ↦ Pic(X_T) / f_T^* Pic(T)` of the Picard presheaf by the classes
from the base; the relative Picard functor `Pic_{X/S}` is its fppf sheafification. -/
noncomputable def picardQuotientPresheaf (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := (pullback f T.unop.hom).Pic ⧸ picardBaseClasses f T.unop
  map φ := TypeCat.ofHom (QuotientGroup.map _ _ (Pic.mapHom (baseChangeMap f φ.unop))
    (picardBaseClasses_le_comap f φ.unop))
  map_id T := by
    refine congrArg TypeCat.ofHom (funext fun x ↦ QuotientGroup.induction_on x fun L ↦ ?_)
    simp only [unop_id, baseChangeMap_id, QuotientGroup.map_mk, Pic.mapHom_apply, Pic.map_id]
    rfl
  map_comp φ ψ := by
    refine congrArg TypeCat.ofHom (funext fun x ↦ QuotientGroup.induction_on x fun L ↦ ?_)
    simp only [unop_comp, baseChangeMap_comp, QuotientGroup.map_mk, Pic.mapHom_apply,
      Pic.map_comp]
    rfl

/-- The quotient map `Pic(X_T) ⟶ Pic(X_T) / f_T^* Pic(T)`, natural in `T`. -/
noncomputable def toPicardQuotientPresheaf (f : X ⟶ S) :
    picardPresheaf f ⟶ picardQuotientPresheaf f where
  app T := TypeCat.ofHom (QuotientGroup.mk' (picardBaseClasses f T.unop) :
    (pullback f T.unop.hom).Pic → (pullback f T.unop.hom).Pic ⧸ picardBaseClasses f T.unop)
  naturality T T' φ := by
    ext L
    exact (QuotientGroup.map_mk (picardBaseClasses f T.unop) (picardBaseClasses f T'.unop)
      (Pic.mapHom (baseChangeMap f φ.unop)) (picardBaseClasses_le_comap f φ.unop) L).symm

end AlgebraicGeometry
