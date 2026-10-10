/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.SectionTransport
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.InternalHom

/-!
# Transport of sections along members of the pro-étale site and monoidal structures

Let `V ∈ X_proét` with structure morphism `g : V ⟶ X`. The sections of a sheaf `F` over `V` are
the global sections of `g^* F` (`AlgebraicGeometry.ProEtale.sectionTransport`). This file shows
that this identification is compatible with the monoidal structure of `g^*`: it sends the unit
sections of `𝟙_` to the unit sections, and pure tensors `x ⊗ y` of sections to pure tensors.

## Main results

- `AlgebraicGeometry.ProEtale.tensorSection_eq_μ`: the comparison `tensorSection` is the tensor
  comparison of the lax monoidal functor `sheafToPresheaf`.
- `AlgebraicGeometry.ProEtale.δ_upperStar_sectionTransport_tensorSectionMap`: the comparison
  `g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` sends the transport of `x ⊗ y` to the tensor of the transports.
- `AlgebraicGeometry.ProEtale.η_upperStar_sectionTransport_unitSection`: the comparison
  `g^* 𝟙_ ⟶ 𝟙_` sends the transport of a unit section to the unit section.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The comparison `tensorSection F G : F ⊗ G ⟶ (F ⊗ G)` from the objectwise tensor product is
the tensor comparison of the lax monoidal functor `sheafToPresheaf`. -/
lemma tensorSection_eq_μ (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    tensorSection F G = μ (sheafToPresheaf _ _) F G :=
  rfl

/-- The constant sections of the unit sheaf are the unit comparison of the lax monoidal functor
`sheafToPresheaf`. -/
lemma unitSection_eq_ε :
    unitSection (X := X) (Λ := Λ) = ε (sheafToPresheaf _ _) :=
  rfl

/-- `sectionTransport` is the inverse of the identification `g^* ≅ j^*` applied to the
restriction along `map(V) ≅ V`. -/
lemma sectionTransport_hom_eq (V : X.ProEt)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (y : G.obj.obj (op V)) :
    (sectionTransport V G).hom y =
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop).inv.app G).hom.app
        (op (terminalProEt V.left)) (G.obj.map (Scheme.ProEt.overMapMkIdIso V).hom.op y) :=
  rfl

/-- The comparison `η : g^* 𝟙_ ⟶ 𝟙_` sends the transport of the unit section `r` over `V` to
the unit section `r` over the terminal object. -/
lemma η_upperStar_sectionTransport_unitSection (V : X.ProEt) (r : Λ) :
    (η (V.hom)^*[ModuleCat.{u + 1} Λ]).hom.app (op (terminalProEt V.left))
        ((sectionTransport V (𝟙_ _)).hom ((unitSection (X := X)).app (op V) r)) =
      (unitSection (X := V.left)).app (op (terminalProEt V.left)) r := by
  have : (MorphismProperty.Over.map ⊤ V.prop).IsContinuous (Scheme.ProEt.topology V.left)
      (Scheme.ProEt.topology X) := Scheme.ProEt.isContinuous_overMap V.prop
  let φ := upperStarIsoSheafPushforward (ModuleCat.{u + 1} Λ) V.hom V.prop
  have hU := NatTrans.IsMonoidal.unit (τ := φ.hom)
  have key : ε _ ≫ φ.inv.app (𝟙_ _) ≫ η (V.hom)^*[ModuleCat.{u + 1} Λ] = 𝟙 _ := by
    rw [← hU, Category.assoc, Iso.hom_inv_id_app_assoc, Functor.Monoidal.ε_η]
  have hR := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (MorphismProperty.Over.map ⊤ V.prop) (ModuleCat.{u + 1} Λ) (Scheme.ProEt.topology V.left)
    (Scheme.ProEt.topology X) (op (terminalProEt V.left))
  rw [sectionTransport_hom_eq, unitSection_app_map, unitSection_eq_ε]
  erw [← ConcreteCategory.congr_hom hR r]
  rw [ConcreteCategory.comp_apply]
  erw [← Sheaf.comp_hom_app_apply, ← Sheaf.comp_hom_app_apply, key]
  rfl


/-- The comparison `tensorSectionMap` is natural in both sheaves. -/
lemma tensorHom_hom_app_tensorSectionMap {F F' G G' : Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') (g : G ⟶ G') (V : X.ProEt) (x : F.obj.obj (op V))
    (y : G.obj.obj (op V)) :
    (f ⊗ₘ g).hom.app (op V) (tensorSectionMap F G V (x ⊗ₜ y)) =
      tensorSectionMap F' G' V (f.hom.app (op V) x ⊗ₜ g.hom.app (op V) y) :=
  (ConcreteCategory.congr_hom
    (NatTrans.congr_app (μ_natural (sheafToPresheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)) f g) (op V)) (x ⊗ₜ y)).symm

/-- The comparison `δ : g^*(F ⊗ G) ⟶ g^* F ⊗ g^* G` sends the transport of a pure tensor
`x ⊗ y` of sections over `V` to the pure tensor of the transports. -/
lemma δ_upperStar_sectionTransport_tensorSectionMap (V : X.ProEt)
    (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (x : F.obj.obj (op V))
    (y : G.obj.obj (op V)) :
    (δ (V.hom)^*[ModuleCat.{u + 1} Λ] F G).hom.app (op (terminalProEt V.left))
        ((sectionTransport V (F ⊗ G)).hom (tensorSectionMap F G V (x ⊗ₜ y))) =
      tensorSectionMap _ _ (terminalProEt V.left)
        ((sectionTransport V F).hom x ⊗ₜ (sectionTransport V G).hom y) := by
  have : (MorphismProperty.Over.map ⊤ V.prop).IsContinuous (Scheme.ProEt.topology V.left)
      (Scheme.ProEt.topology X) := Scheme.ProEt.isContinuous_overMap V.prop
  let φ := upperStarIsoSheafPushforward (ModuleCat.{u + 1} Λ) V.hom V.prop
  have hT := NatTrans.IsMonoidal.tensor (τ := φ.hom) F G
  have key : μ _ F G ≫ φ.inv.app (F ⊗ G) ≫ δ (V.hom)^*[ModuleCat.{u + 1} Λ] F G =
      φ.inv.app F ⊗ₘ φ.inv.app G := by
    rw [← cancel_epi (φ.hom.app F ⊗ₘ φ.hom.app G)]
    erw [← reassoc_of% hT]
    rw [Iso.hom_inv_id_app_assoc, Functor.Monoidal.μ_δ, tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
      tensorHom_id, id_whiskerRight]
  have hR := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.map ⊤ V.prop) (ModuleCat.{u + 1} Λ) (Scheme.ProEt.topology V.left)
    (Scheme.ProEt.topology X) F G (op (terminalProEt V.left))
  rw [sectionTransport_hom_eq, tensorSectionMap_naturality]
  erw [← ConcreteCategory.congr_hom hR]
  rw [ConcreteCategory.comp_apply]
  erw [← Sheaf.comp_hom_app_apply, ← Sheaf.comp_hom_app_apply, key]
  exact tensorHom_hom_app_tensorSectionMap _ _ _ _ _


/-- The pullback along `g : V ⟶ X` of a morphism `f : 𝟙_ ⟶ H` out of the unit, precomposed with
`𝟙_ ≅ g^* 𝟙_`, corresponds to the transport of the restriction to `V` of the section `f(1)`. -/
lemma sectionOfUnitHom_upperStar_map (V : X.ProEt)
    {H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (f : 𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶ H) :
    sectionOfUnitHom (inv (η (V.hom)^*[ModuleCat.{u + 1} Λ]) ≫ (V.hom)^*[ModuleCat.{u + 1} Λ].map f) =
      (sectionTransport V H).hom
        (H.obj.map ((Scheme.ProEt.isTerminalMkId X).from V).op (sectionOfUnitHom f)) := by
  have h := η_upperStar_sectionTransport_unitSection V (1 : Λ)
  have h' : (inv (η (V.hom)^*[ModuleCat.{u + 1} Λ])).hom.app (op (terminalProEt V.left))
      ((unitSection (X := V.left)).app (op (terminalProEt V.left)) (1 : Λ)) =
      (sectionTransport V (𝟙_ _)).hom ((unitSection (X := X)).app (op V) (1 : Λ)) := by
    rw [← h, ← Sheaf.comp_hom_app_apply, IsIso.hom_inv_id, Sheaf.id_hom_app_apply]
  rw [sectionOfUnitHom, NatTrans.comp_app, ConcreteCategory.comp_apply, Sheaf.comp_hom_app_apply]
  erw [h']
  erw [← sectionTransport_naturality]
  congr 1
  rw [sectionOfUnitHom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    ← unitSection_app_map ((Scheme.ProEt.isTerminalMkId X).from V)]
  exact NatTrans.naturality_apply f.hom _ _

end AlgebraicGeometry.ProEtale
