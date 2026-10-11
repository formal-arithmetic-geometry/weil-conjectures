/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar

/-!
# Restriction of scalars and the base change map

Let `φ : Λ →+* Λ'` be a morphism of commutative rings. Restriction of scalars along `φ`
commutes with the pushforwards `g_*` of étale sheaves (both are computed objectwise), and,
taking mates along `g^* ⊣ g_*`, it commutes with the pullbacks: the mate
`AlgebraicGeometry.Etale.upperStarRestrictScalars φ g : g^*(res G) ⟶ res(g^* G)` is an
isomorphism (`AlgebraicGeometry.Etale.isIso_upperStarRestrictScalars`), since its conjugate
along the adjunctions `res ⊣ coext` is the identification of `g_* ∘ coext` with
`coext ∘ g_*`.

Through these identifications, the base change map `g^* f_* ⟶ f'_* g'^*` of a commutative
square over `Λ'` is carried by restriction of scalars to the one over `Λ`
(`AlgebraicGeometry.Etale.baseChangeMap_app_restrictScalars`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- The unit of `res ⊣ coext` on étale sheaves is computed sectionwise. -/
lemma restrictCoextendScalarsAdj_unit_app_hom_app {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (U : X.Etaleᵒᵖ) :
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.app G).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).unit.app (G.obj.obj U) := by
  change ((sheafToPresheaf X.smallEtaleTopology _).map
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.app G)).app U = _
  rw [Sheaf.restrictCoextendScalarsAdj, Adjunction.map_restrictFullyFaithful_unit_app]
  simp

/-- The counit of `res ⊣ coext` on étale sheaves is computed sectionwise. -/
lemma restrictCoextendScalarsAdj_counit_app_hom_app {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : X.Etaleᵒᵖ) :
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).counit.app G).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).counit.app (G.obj.obj U) := by
  change ((sheafToPresheaf X.smallEtaleTopology _).map
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).counit.app G)).app U = _
  rw [Sheaf.restrictCoextendScalarsAdj, Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [Functor.comp_obj, Functor.id_obj, Iso.refl_inv, NatTrans.id_app,
    NatTrans.comp_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

section Pullback

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The comparison `g^*(res G) ⟶ res(g^* G)` between the pullback along `g` and restriction of
scalars along `φ`: the mate, along the adjunctions `g^* ⊣ g_*`, of the identification
`g_* ∘ res = res ∘ g_*` (`AlgebraicGeometry.Etale.lowerStarCompRestrictScalarsIso`). -/
noncomputable def upperStarRestrictScalars :
    TwoSquare (Sheaf.restrictScalars Y.smallEtaleTopology φ) (g)^*[ModuleCat.{u + 1} Λ']
      (g)^*[ModuleCat.{u + 1} Λ] (Sheaf.restrictScalars Z.smallEtaleTopology φ) :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)).symm
      (TwoSquare.mk _ _ _ _ (lowerStarCompRestrictScalarsIso φ g).hom)

/-- **The unit form of the comparison of pullbacks**: for a sheaf `G` of `Λ'`-modules on `Y`,
`res(η G) = η(res G) ≫ g_*(upperStarRestrictScalars G)`. -/
lemma restrictScalars_map_unit_app (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g).unit.app G) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
          ((Sheaf.restrictScalars Y.smallEtaleTopology φ).obj G) ≫
        (g)_*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalars φ g).natTrans.app G) := by
  have := unit_mateEquiv_symm (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (TwoSquare.mk _ _ _ _ (lowerStarCompRestrictScalarsIso φ g).hom) G
  exact (Category.comp_id _).symm.trans this

/-- The mate of the identification `coext ∘ g_* = g_* ∘ coext` along the adjunctions
`res ⊣ coext` is the identification `g_* ∘ res = res ∘ g_*`. -/
lemma mateEquiv_symm_lowerStarCompCoextendScalarsIso :
    (mateEquiv (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)
      (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ)).symm
        (TwoSquare.mk _ _ _ _ (lowerStarCompCoextendScalarsIso φ g).inv) =
      TwoSquare.mk _ _ _ _ (lowerStarCompRestrictScalarsIso φ g).hom := by
  ext G U : 4
  simp only [Functor.comp_obj, mateEquiv_symm_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, Functor.associator_hom_app, CategoryTheory.Functor.map_id,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, sheafCompose_map_hom,
    restrictCoextendScalarsAdj_counit_app_hom_app, lowerStarCompCoextendScalarsIso,
    lowerStarCompRestrictScalarsIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  rw [Etale.lowerStar_map_hom_app, restrictCoextendScalarsAdj_unit_app_hom_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).left_triangle_components _

/-- **Pullback commutes with restriction of scalars**: the comparison
`g^*(res G) ⟶ res(g^* G)` is an isomorphism. Its conjugate along the adjunctions
`res ⊣ coext` is the identification of `g_* ∘ coext` with `coext ∘ g_*`
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv_symm`). -/
instance isIso_upperStarRestrictScalars : IsIso (upperStarRestrictScalars φ g).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ)
    (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)
    (TwoSquare.mk _ _ _ _ (lowerStarCompCoextendScalarsIso φ g).inv)
  rw [mateEquiv_symm_lowerStarCompCoextendScalarsIso] at h
  rw [upperStarRestrictScalars, h]
  have : IsIso ((conjugateEquiv ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g).comp
      (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ))
      ((Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g))).symm
      (lowerStarCompCoextendScalarsIso φ g).inv) := inferInstance
  exact this

end Pullback

end Etale

end AlgebraicGeometry
