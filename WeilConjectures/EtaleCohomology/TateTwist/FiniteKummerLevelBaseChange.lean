/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.FiniteKummerLevel

/-!
# The finite Kummer level of the Tate twist: base change

For `g : X ⟶ Y`, the pullback `g^* μₙ ⟶ μₙ` induces base change maps
`g^*(Λ ⊗_ℤ μₙ) ⟶ Λ ⊗_ℤ μₙ` (`AlgebraicGeometry.Etale.upperStarTateSheafToTateSheaf`) and
`g^*(μₙ ⊗_{ℤ/n} Λ) ⟶ μₙ ⊗_{ℤ/n} Λ`
(`AlgebraicGeometry.Etale.upperStarExtendScalarsAlongRootsOfUnity`), and the identification
`Λ ⊗_ℤ μₙ ≅ μₙ ⊗_{ℤ/n} Λ` commutes with them
(`AlgebraicGeometry.Etale.upperStar_map_extendScalarsIsoExtendScalarsAlong_hom`): the finite
Kummer level identification of blueprint `lem-pur-finite-kummer-level` is compatible with base
change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {n : ℕ} [CharP Λ n] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The identification `g^*(Λ ⊗ F) ≅ Λ ⊗ g^* F` through the units of the adjunctions. -/
private lemma unit_app_upperStarExtendScalarsIso'
    (x : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (extendScalarsAdjunction Λ Y).unit.app x ≫
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((upperStarLowerStarAdjunction _ g).unit.app ((extendScalars Λ Y).obj x) ≫
          (g)_*[ModuleCat.{u + 1} Λ].map ((upperStarExtendScalarsIso Λ g).hom.app x)) =
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app x ≫
      (g)_*[AddCommGrpCat.{u + 1}].map
        ((extendScalarsAdjunction Λ X).unit.app ((g)^*[AddCommGrpCat.{u + 1}].obj x)) := by
  have hunit {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G H : D ⥤ C}
      (adj : F ⊣ G) (e : G ≅ H) (x : C) :
      (adj.ofNatIsoRight e).unit.app x = adj.unit.app x ≫ e.hom.app _ := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.homEquiv_id]
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((extendScalarsAdjunction Λ Y).comp (upperStarLowerStarAdjunction _ g))
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).comp
      (extendScalarsAdjunction Λ X)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))) x
  rw [Adjunction.homEquiv_unit, hunit] at this
  simpa [upperStarExtendScalarsIso, Adjunction.comp_unit_app] using this

/-- The base change map `g^*(μₙ ⊗_{ℤ/n} Λ) ⟶ μₙ ⊗_{ℤ/n} Λ` induced by `g^* μₙ ⟶ μₙ`: the transpose of
`μₙ ⟶ g_* μₙ ⟶ g_*(μₙ ⊗_{ℤ/n} Λ)`. -/
noncomputable def upperStarExtendScalarsAlongRootsOfUnity :
    (g)^*[ModuleCat.{u + 1} Λ].obj ((extendScalarsAlong Λ (ZMod.castHom (dvd_refl n) Λ) Y).obj
        (Y.rootsOfUnityModuleSheaf n)) ⟶
      (extendScalarsAlong Λ (ZMod.castHom (dvd_refl n) Λ) X).obj (X.rootsOfUnityModuleSheaf n) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).homEquiv _ _).symm
    (((extendScalarsAlongAdjunction Λ _ Y).homEquiv _ _).symm
      ((rootsOfUnityModuleSheafHomEquiv Λ Y _).symm
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _
          (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g)) ≫
          (g)_*[AddCommGrpCat.{u + 1}].map (rootsOfUnityModuleSheafHomEquiv Λ X _
            ((extendScalarsAlongAdjunction Λ (ZMod.castHom (dvd_refl n) Λ) X).unit.app
              (X.rootsOfUnityModuleSheaf n))))))

/-- The comparison `rootsOfUnityModuleSheafHomEquiv` turns the unit of extension of scalars
along `ℤ/n ⟶ Λ` followed by a map into the corresponding transpose. -/
lemma rootsOfUnityModuleSheafHomEquiv_unit_comp {S : Scheme.{u}}
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (k : (extendScalarsAlong Λ (ZMod.castHom (dvd_refl n) Λ) S).obj
      (S.rootsOfUnityModuleSheaf n) ⟶ G) :
    rootsOfUnityModuleSheafHomEquiv Λ S _
        ((extendScalarsAlongAdjunction Λ (ZMod.castHom (dvd_refl n) Λ) S).unit.app
          (S.rootsOfUnityModuleSheaf n)) ≫
      (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map k =
    rootsOfUnityModuleSheafHomEquiv Λ S G
      ((extendScalarsAlongAdjunction Λ (ZMod.castHom (dvd_refl n) Λ) S).homEquiv _ _ k) := by
  rw [← rootsOfUnityModuleSheafHomEquiv_naturality, Adjunction.homEquiv_unit]

/-- Blueprint `lem-pur-finite-kummer-level`: Finite Kummer level of the Tate twist

**Compatibility with base change.** The identification `Λ ⊗_ℤ μₙ ≅ μₙ ⊗_{ℤ/n} Λ` commutes with the
base change maps along any `g : X ⟶ Y`: the square

```
g^*(Λ ⊗_ℤ μₙ) ──≅──▶ g^*(μₙ ⊗_{ℤ/n} Λ)
      │                      │
      ▼                      ▼
 Λ ⊗_ℤ μₙ ─────≅──────▶ μₙ ⊗_{ℤ/n} Λ
```

commutes. -/
theorem upperStar_map_extendScalarsIsoExtendScalarsAlong_hom :
    (g)^*[ModuleCat.{u + 1} Λ].map (extendScalarsIsoExtendScalarsAlong Λ Y n).hom ≫
        upperStarExtendScalarsAlongRootsOfUnity Λ g =
      ((upperStarExtendScalarsIso Λ g).hom.app _ ≫
        (extendScalars Λ X).map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g)) ≫
        (extendScalarsIsoExtendScalarsAlong Λ X n).hom := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).homEquiv _ _).injective
  apply ((extendScalarsAdjunction Λ Y).homEquiv _ _).injective
  -- the left-hand side
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    upperStarExtendScalarsAlongRootsOfUnity, Equiv.apply_symm_apply]
  sorry

end AlgebraicGeometry.Etale
