/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Derived.DualizableLocalRetract
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.InternalHom

/-!
# Transporting sections along the members of the small pro-étale site

Let `V ∈ X_proét` with structure morphism `g : V ⟶ X`. The sections of a pro-étale sheaf `G`
over `V` are the global sections of `g^* G` on the small pro-étale site of `V`
(`AlgebraicGeometry.ProEtale.sectionTransport`). This file records how this identification
interacts with constant sheaves.

## Main results

- `AlgebraicGeometry.ProEtale.constantSheaf_hom_ext`: morphisms out of a constant sheaf are
  determined by the images of the constant global sections.
- `AlgebraicGeometry.ProEtale.upperStarConstantSheafIso_hom_sectionTransport`: the identification
  `g^* c_X(E) ≅ c_V(E)` sends the transport of a constant section to the constant section.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The constant section `e` of the constant sheaf `c(E)` over `U`. -/
noncomputable def constSection (E : ModuleCat.{u + 1} Λ) (U : X.ProEt) (e : E) :
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj E).obj.obj (op U) :=
  (toSheafify (Scheme.ProEt.topology X) ((Functor.const _).obj E)).app (op U) e

/-- Constant sections restrict to constant sections. -/
lemma constSection_map (E : ModuleCat.{u + 1} Λ) {U V : X.ProEt} (f : V ⟶ U) (e : E) :
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj E).obj.map f.op
      (constSection E U e) = constSection E V e :=
  (NatTrans.naturality_apply (toSheafify (Scheme.ProEt.topology X) ((Functor.const _).obj E))
    f.op e).symm

/-- The adjunction `c ⊣ Γ` sends a morphism out of `c(E)` to its values on the constant
global sections. -/
lemma constantSheafAdjunction_homEquiv_apply {E : ModuleCat.{u + 1} Λ}
    {H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (φ : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj E ⟶ H) (e : E) :
    ((constantSheafAdjunction X).homEquiv _ _ φ) e =
      φ.hom.app (op (terminalProEt X)) (constSection E _ e) := by
  simp [constantSheafAdjunction, constantSheafAdj, Adjunction.comp_homEquiv, constSection,
    constantPresheafAdj]
  rfl

/-- Morphisms out of a constant sheaf are determined by the images of the constant global
sections. -/
lemma constantSheaf_hom_ext {E : ModuleCat.{u + 1} Λ}
    {H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    {φ₁ φ₂ : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj E ⟶ H}
    (h : ∀ e, φ₁.hom.app (op (terminalProEt X)) (constSection E _ e) =
      φ₂.hom.app (op (terminalProEt X)) (constSection E _ e)) : φ₁ = φ₂ := by
  apply ((constantSheafAdjunction X).homEquiv _ _).injective
  ext e
  rw [constantSheafAdjunction_homEquiv_apply, constantSheafAdjunction_homEquiv_apply, h]

lemma constantSheafAdjunction_unit_app_apply (E : ModuleCat.{u + 1} Λ) (e : E) :
    ((constantSheafAdjunction X).unit.app E) e = constSection E (terminalProEt X) e := by
  have := constantSheafAdjunction_homEquiv_apply (X := X) (𝟙 ((constantSheaf _ _).obj E)) e
  rw [Adjunction.homEquiv_id] at this
  exact this

/-- The identification `g^* c_Y(E) ≅ c_Z(E)` sends the image under the unit of `g^* ⊣ g_*` of a
constant global section to the constant section. -/
lemma upperStarConstantSheafIso_hom_app_unit {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (E : ModuleCat.{u + 1} Λ) (e : E) :
    (((g)_*[ModuleCat.{u + 1} Λ].map ((upperStarConstantSheafIso g).hom.app E)).hom.app
        (op (terminalProEt Y)))
      ((((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
          ((constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).obj E)).hom.app
            (op (terminalProEt Y))) (constSection E (terminalProEt Y) e)) =
      (by exact constSection E _ e) := by
  have h := congrArg (fun φ ↦ φ e) (Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((constantSheafAdjunction Y).comp (upperStarLowerStarAdjunction _ g))
    ((constantSheafAdjunction Z).ofNatIsoRight (sectionsLowerStarIso g)) E)
  rw [show ((constantSheafAdjunction Y).comp (upperStarLowerStarAdjunction _ g)).leftAdjointUniq
    ((constantSheafAdjunction Z).ofNatIsoRight (sectionsLowerStarIso g))
      = upperStarConstantSheafIso g from rfl] at h
  rw [Adjunction.comp_homEquiv] at h
  erw [Equiv.trans_apply] at h
  erw [constantSheafAdjunction_homEquiv_apply] at h
  erw [Adjunction.homEquiv_unit] at h
  have hU := Adjunction.homEquiv_ofNatIsoRight_apply (constantSheafAdjunction Z)
    (sectionsLowerStarIso g) (𝟙 ((constantSheaf _ _).obj E))
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_id] at hU
  rw [hU] at h
  refine h.trans ?_
  rw [ConcreteCategory.comp_apply]
  erw [constantSheafAdjunction_unit_app_apply]
  exact constSection_map E _ e

/-- For `V ∈ X_proét` with structure morphism `g`, the sections of a sheaf `G` over `V` are the
global sections of `g^* G`. -/
noncomputable def sectionTransport (V : X.ProEt)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    G.obj.obj (op V) ≅
      ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G).obj.obj (op (terminalProEt V.left)) :=
  ((upperStarSectionsMkIdIso _ V).app G).symm

/-- `sectionTransport` is natural in the sheaf. -/
lemma sectionTransport_naturality (V : X.ProEt)
    {G H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (φ : G ⟶ H)
    (x : G.obj.obj (op V)) :
    (sectionTransport V H).hom (φ.hom.app (op V) x) =
      ((V.hom)^*[ModuleCat.{u + 1} Λ].map φ).hom.app (op (terminalProEt V.left))
        ((sectionTransport V G).hom x) := by
  have := (upperStarSectionsMkIdIso (ModuleCat.{u + 1} Λ) V).inv.naturality φ
  exact ConcreteCategory.congr_hom this x

set_option backward.isDefEq.respectTransparency false in
/-- `sectionTransport` in terms of the restriction `j^*`: it is the inverse of the identification
`g^* ≅ j^*` applied to the restriction along `map(V) ≅ V`. -/
lemma upperStarIsoLocalizationRestriction_hom_sectionTransport (V : X.ProEt)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (y : G.obj.obj (op V)) :
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop).hom.app G).hom.app
        (op (terminalProEt V.left)) ((sectionTransport V G).hom y) =
      G.obj.map (Scheme.ProEt.overMapMkIdIso V).hom.op y := by
  have hST : (sectionTransport V G).hom y =
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop).inv.app G).hom.app
        (op (terminalProEt V.left)) (G.obj.map (Scheme.ProEt.overMapMkIdIso V).hom.op y) := rfl
  rw [hST, ← Sheaf.comp_hom_app_apply, Iso.inv_hom_id_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The transport of the restriction to `V` of a global section `x` is the restriction of
`unit_g(x)` along `V.left ≅ V.left ×_X X`. -/
lemma sectionTransport_map (V : X.ProEt)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (x : G.obj.obj (op (terminalProEt X))) :
    (sectionTransport V G).hom (G.obj.map ((Scheme.ProEt.isTerminalMkId X).from V).op x) =
      ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G).obj.map
        (overPullbackObjMkIdIso V.hom).inv.op
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) V.hom).unit.app G).hom.app
          (op (terminalProEt X)) x) := by
  let iso := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop
  apply (ConcreteCategory.bijective_of_isIso ((iso.hom.app G).hom.app _)).1
  rw [upperStarIsoLocalizationRestriction_hom_sectionTransport]
  erw [Sheaf.hom_app_map_apply]
  have h := Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} Λ) V.hom) (localizationRestrictionLowerStarAdjunction _ V.hom V.prop) G
  have h' := congrArg (fun φ ↦ φ.hom.app (op (terminalProEt X)) x) h
  dsimp only at h'
  erw [localizationRestrictionLowerStarAdjunction_unit_app_hom_app] at h'
  erw [h']
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun k ↦ (G.obj.map k.op) x) ((Scheme.ProEt.isTerminalMkId X).hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The identification `g^* c_X(E) ≅ c_V(E)` sends the transport of a constant section over `V`
to the constant section. -/
lemma upperStarConstantSheafIso_hom_sectionTransport (V : X.ProEt) (E : ModuleCat.{u + 1} Λ)
    (e : E) :
    ((upperStarConstantSheafIso V.hom).hom.app E).hom.app (op (terminalProEt V.left))
      ((sectionTransport V ((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} Λ)).obj E)).hom (constSection E V e)) =
        constSection E (terminalProEt V.left) e := by
  have h1 := sectionTransport_map V
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj E)
    (constSection E (terminalProEt X) e)
  rw [constSection_map] at h1
  rw [h1]
  erw [Sheaf.hom_app_map_apply]
  erw [upperStarConstantSheafIso_hom_app_unit V.hom E e]
  exact constSection_map E _ e

end AlgebraicGeometry.ProEtale
