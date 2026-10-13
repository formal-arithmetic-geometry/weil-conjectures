/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechModel

/-! # Coefficient comparison by the composed adjunction

Source: Stacks Project, Tags 02KE, 01I9, 01IA and 0097.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pull sections back by the unit, then restrict to the support of the direct image.
Source: Stacks Project, Tag 0097, restriction of a pullback section. -/
def coefficientSectionAddMap {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) (U : T.Opens) (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (_w : g' ≫ f = f' ≫ (g ≫ U.ι)) (W : X'.Opens)
    (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) :
    Γ(F.restrict (f ⁻¹ᵁ U).ι, Z) →+
      Γ((pushforward U.toScheme.toSpecΓ).obj
        ((pushforward g).obj ((pushforward (W.ι ≫ f')).obj
          (((pullback g').obj F).restrict W.ι))), ⊤) := by
  let B := g ⁻¹ᵁ (U.toScheme.toSpecΓ ⁻¹ᵁ ⊤)
  let L := W.ι ''ᵁ ((W.ι ≫ f') ⁻¹ᵁ B)
  have hL : L ≤ g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z) := by
    dsimp [L]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_le_left.trans hW.le
  exact (((pullback g').obj F).presheaf.map (homOfLE hL).op).hom.comp
    ((((pullbackPushforwardAdjunction g').unit.app F).app
      ((f ⁻¹ᵁ U).ι ''ᵁ Z)).hom.comp ((F.restrictAppIso (f ⁻¹ᵁ U).ι Z).hom.hom))

/-- The section-unit map is linear for the structural map of the base.
Source: Stacks Project, Tag 0096, module pullback adjunction; Tag 0097, composition.
(blueprint: lem-pc-coefficient-section-map-linear).
Proof: The source scalar is first restricted along the global structural map and
then to Z. The restriction identification transports it through the inverse of
Y.ι.appIso. The pullback unit is linear over the section ring on Y.ι(Z), with
target scalars transported by g'. Restricting to the support transports it once
more. On the target the scalar is transported successively by GammaSpecIso.inv,
U.toSpecGamma, g, fprime and W.ι, followed by W.ι.appIso.inv. Naturality of the
structure maps, the equality gprime f = fprime g U.ι, and the inverse identities
of appIso identify these two composites. Thus both scalar actions agree. Empty
opens cause no exception since restriction maps and linearity remain defined. -/
theorem coefficientSectionAddMap_linear {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) (U : T.Opens) (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι)) (W : X'.Opens)
    (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) :
    let N := (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
      ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
    let P := moduleSpecΓFunctor.obj ((pushforward U.toScheme.toSpecΓ).obj
      ((pushforward g).obj ((pushforward (W.ι ≫ f')).obj
        (((pullback g').obj F).restrict W.ι))))
    ∀ (a : Γ(U.toScheme, ⊤)) (s : N),
      coefficientSectionAddMap f F U Z g g' f' w W hW (a • s) =
        a • (show P from coefficientSectionAddMap f F U Z g g' f' w W hW s) := by
  sorry

/-- The linear map of sections used as the mate in the composed adjunction.
Source: Stacks Project, Tag 02KE, termwise coefficient construction. -/
def coefficientSectionLinearMap {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) (U : T.Opens) (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι)) (W : X'.Opens)
    (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) :
    (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
      ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z)) ⟶
    moduleSpecΓFunctor.obj ((pushforward U.toScheme.toSpecΓ).obj
      ((pushforward g).obj ((pushforward (W.ι ≫ f')).obj
        (((pullback g').obj F).restrict W.ι)))) :=
  ConcreteCategory.ofHom (C := ModuleCat Γ(U.toScheme, ⊤))
    { toFun := coefficientSectionAddMap f F U Z g g' f' w W hW
      map_add' := (coefficientSectionAddMap f F U Z g g' f' w W hW).map_add
      map_smul' := coefficientSectionAddMap_linear f F U Z g g' f' w W hW }

/-- The coefficient morphism is the mate of the explicit linear map of sections.
Source: Stacks Project, Tags 02KE and 01IA, adjunction construction. -/
def coefficientComparisonMorphism {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) (U : T.Opens) (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι)) (W : X'.Opens)
    (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) :
    (pullback g).obj ((pullback U.toScheme.toSpecΓ).obj
      (tilde ((ModuleCat.restrictScalars
        (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
          ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
        ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))))) ⟶
    (pushforward (W.ι ≫ f')).obj (((pullback g').obj F).restrict W.ι) :=
  (((tilde.adjunction (R := Γ(U.toScheme, ⊤))).comp
    (pullbackPushforwardAdjunction U.toScheme.toSpecΓ)).comp
      (pullbackPushforwardAdjunction g)).homEquiv _ _ |>.symm
        (coefficientSectionLinearMap f F U Z g g' f' w W hW)

end
end AlgebraicGeometry.Scheme.Modules
