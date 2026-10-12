/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Linearity of the underived exchange morphism

Source: Stacks Project, Etale Cohomology, Tag 03S6, proof; Modules on Sites,
Tags 03D3, 03D7, 03D8 (blueprint: lem-weil-pbc-underived-exchange-module-linear).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The abelian exchange lifts to a natural transformation of constant-ring module sheaves.
Source: Stacks Project, Tag 03S6, proof, and Tags 03D3, 03D7, 03D8
(blueprint: lem-weil-pbc-underived-exchange-module-linear).

The lambda-bound ring sheaves are the constant sheaves; direct images are the existing
module pushforwards. The universally quantified inverse images,
comparison isomorphisms and compatible adjunctions are precisely the data supplied by
`etaleInverseImageModulesExact`; the conditions on gamma specify the constant-ring map.
They allow any choice of the canonical inverse image rather than fixing a chosen witness.
The comparison formula says that every component of the lifted transformation is the
abelian exchange map, after identifying the underlying abelian inverse images.

Proof:
1. The square isomorphism is the inverse of one inverse-image composition isomorphism
   followed by the other (def-weil-pbc-cartesian-square). Both are linear by
   lem-weil-pbc-inverse-image-composition-module-linear, so their composite is linear.
2. The module counit is the abelian counit by prop-weil-pbc-inverse-image-modules-exact.
   Its inverse image along g' is linear, so its composite with the square isomorphism
   is linear (def-weil-pbc-underived-exchange).
3. The compatible module adjunction for f' sends that linear composite to a linear map;
   after forgetting it is the abelian underived exchange (Tag 03D3).
4. The abelian naturality equality of lemma-weil-pbc-underived-exchange-naturality
   is the same equality of module maps since the forgetful functor is faithful.
   These components therefore give the asserted natural transformation. -/
theorem etaleUnderivedExchange_moduleLinear
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (R : CommRingCat.{u + 1}) :
    (fun (RX : Sheaf X.smallEtaleTopology RingCat.{u + 1})
      (RY : Sheaf Y.smallEtaleTopology RingCat.{u + 1})
      (RX' : Sheaf X'.smallEtaleTopology RingCat.{u + 1})
      (RY' : Sheaf Y'.smallEtaleTopology RingCat.{u + 1})
      (etaX : ((Functor.const X.Etaleᵒᵖ).obj
        ((forget₂ CommRingCat RingCat).obj R)) ⟶ RX.obj)
      (etaY : ((Functor.const Y.Etaleᵒᵖ).obj
        ((forget₂ CommRingCat RingCat).obj R)) ⟶ RY.obj)
      (etaX' : ((Functor.const X'.Etaleᵒᵖ).obj
        ((forget₂ CommRingCat RingCat).obj R)) ⟶ RX'.obj)
      (etaY' : ((Functor.const Y'.Etaleᵒᵖ).obj
        ((forget₂ CommRingCat RingCat).obj R)) ⟶ RY'.obj) =>
    ∀ (gamma_f : RY ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        RingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
          (X.smallGrothendieckTopology @Etale)).obj RX),
    (∀ (W : Y.Etaleᵒᵖ) (r : R),
      gamma_f.hom.app W
        (etaY.app W r) =
      etaX.app
          ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj W) r) →
    ∀ (gamma_fp : RY' ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f').sheafPushforwardContinuous
        RingCat.{u + 1} (Y'.smallGrothendieckTopology @Etale)
          (X'.smallGrothendieckTopology @Etale)).obj RX'),
    (∀ (W : Y'.Etaleᵒᵖ) (r : R),
      gamma_fp.hom.app W
        (etaY'.app W r) =
      etaX'.app
          ((MorphismProperty.Over.pullback @Etale ⊤ f').op.obj W) r) →
    ∀ (gamma_g : RY ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        RingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
          (Y'.smallGrothendieckTopology @Etale)).obj RY'),
    (∀ (W : Y.Etaleᵒᵖ) (r : R),
      gamma_g.hom.app W
        (etaY.app W r) =
      etaY'.app
          ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj W) r) →
    ∀ (gamma_gp : RX ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ g').sheafPushforwardContinuous
        RingCat.{u + 1} (X.smallGrothendieckTopology @Etale)
          (X'.smallGrothendieckTopology @Etale)).obj RX'),
    (∀ (W : X.Etaleᵒᵖ) (r : R),
      gamma_gp.hom.app W
        (etaX.app W r) =
      etaX'.app
          ((MorphismProperty.Over.pullback @Etale ⊤ g').op.obj W) r) →
    ∀ (L_f : SheafOfModules.{u + 1} RY ⥤ SheafOfModules.{u + 1} RX)
      (e_f : L_f ⋙ SheafOfModules.toSheaf RX ≅
        SheafOfModules.toSheaf RY ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f)
      (a_f : L_f ⊣ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma_f)),
    (∀ (M : SheafOfModules.{u + 1} RY) (N : SheafOfModules.{u + 1} RX)
      (h : L_f.obj M ⟶ N),
      (SheafOfModules.toSheaf RY).map (a_f.homEquiv M N h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
          ((SheafOfModules.toSheaf RY).obj M) ((SheafOfModules.toSheaf RX).obj N)
          (e_f.inv.app M ≫ (SheafOfModules.toSheaf RX).map h)) →
    ∀ (L_fp : SheafOfModules.{u + 1} RY' ⥤ SheafOfModules.{u + 1} RX')
      (e_fp : L_fp ⋙ SheafOfModules.toSheaf RX' ≅
        SheafOfModules.toSheaf RY' ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f')
      (a_fp : L_fp ⊣ (SheafOfModules.pushforward
        (J := Y'.smallGrothendieckTopology @Etale)
        (K := X'.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f') gamma_fp)),
    (∀ (M : SheafOfModules.{u + 1} RY') (N : SheafOfModules.{u + 1} RX')
      (h : L_fp.obj M ⟶ N),
      (SheafOfModules.toSheaf RY').map (a_fp.homEquiv M N h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').homEquiv
          ((SheafOfModules.toSheaf RY').obj M) ((SheafOfModules.toSheaf RX').obj N)
          (e_fp.inv.app M ≫ (SheafOfModules.toSheaf RX').map h)) →
    ∀ (L_g : SheafOfModules.{u + 1} RY ⥤ SheafOfModules.{u + 1} RY')
      (e_g : L_g ⋙ SheafOfModules.toSheaf RY' ≅
        SheafOfModules.toSheaf RY ⋙ Etale.upperStar AddCommGrpCat.{u + 1} g)
      (a_g : L_g ⊣ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := Y'.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ g) gamma_g)),
    (∀ (M : SheafOfModules.{u + 1} RY) (N : SheafOfModules.{u + 1} RY')
      (h : L_g.obj M ⟶ N),
      (SheafOfModules.toSheaf RY).map (a_g.homEquiv M N h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
          ((SheafOfModules.toSheaf RY).obj M) ((SheafOfModules.toSheaf RY').obj N)
          (e_g.inv.app M ≫ (SheafOfModules.toSheaf RY').map h)) →
    ∀ (L_gp : SheafOfModules.{u + 1} RX ⥤ SheafOfModules.{u + 1} RX')
      (e_gp : L_gp ⋙ SheafOfModules.toSheaf RX' ≅
        SheafOfModules.toSheaf RX ⋙ Etale.upperStar AddCommGrpCat.{u + 1} g')
      (a_gp : L_gp ⊣ (SheafOfModules.pushforward
        (J := X.smallGrothendieckTopology @Etale)
        (K := X'.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ g') gamma_gp)),
    (∀ (M : SheafOfModules.{u + 1} RX) (N : SheafOfModules.{u + 1} RX')
      (h : L_gp.obj M ⟶ N),
      (SheafOfModules.toSheaf RX).map (a_gp.homEquiv M N h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').homEquiv
          ((SheafOfModules.toSheaf RX).obj M) ((SheafOfModules.toSheaf RX').obj N)
          (e_gp.inv.app M ≫ (SheafOfModules.toSheaf RX').map h)) →
    ∃ t :
      SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma_f ⋙ L_g ⟶
      L_gp ⋙ SheafOfModules.pushforward
        (J := Y'.smallGrothendieckTopology @Etale)
        (K := X'.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f') gamma_fp,
      ∀ G : SheafOfModules.{u + 1} RX,
        (SheafOfModules.toSheaf RY').map (t.app G) =
          e_g.hom.app ((SheafOfModules.pushforward
            (J := Y.smallGrothendieckTopology @Etale)
            (K := X.smallGrothendieckTopology @Etale)
            (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma_f).obj G) ≫
          (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
            ((SheafOfModules.toSheaf RX).obj G) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} f').map (e_gp.inv.app G))
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        ((forget₂ CommRingCat RingCat).obj R))
      ((constantSheaf Y.smallEtaleTopology RingCat.{u + 1}).obj
        ((forget₂ CommRingCat RingCat).obj R))
      ((constantSheaf X'.smallEtaleTopology RingCat.{u + 1}).obj
        ((forget₂ CommRingCat RingCat).obj R))
      ((constantSheaf Y'.smallEtaleTopology RingCat.{u + 1}).obj
        ((forget₂ CommRingCat RingCat).obj R))
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj R)))
      (toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj R)))
      (toSheafify X'.smallEtaleTopology
        ((Functor.const X'.Etaleᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj R)))
      (toSheafify Y'.smallEtaleTopology
        ((Functor.const Y'.Etaleᵒᵖ).obj ((forget₂ CommRingCat RingCat).obj R))) := by
  sorry

end AlgebraicGeometry
