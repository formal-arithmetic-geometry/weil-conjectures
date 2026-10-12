/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # EtaleModuleRingIsoAdjunction

Source: Stacks Project, Tags 03D3, 03D6, 03D7.
(blueprint: lem-weil-pbc-etale-module-ring-iso-adjunction). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a linearity criterion through an isomorphism of ring sheaves.
Source: Stacks Project, Tags 03D3 and 03D7, specialized to an invertible ring map.

Proof: let LM be L0 followed by restriction of scalars along c.inv. Restriction
along c.hom and c.inv are inverse equivalences: on sections their composite actions
are the original action, by the two inverse-ring equations. Their identity maps
on abelian groups give the comparison t. Define e by composing t with e0 after
forgetting. A map from LM(G) to F is RU-linear precisely when the same abelian map
from L0(G) to restriction of F along c.hom is Lr(RV)-linear. Apply hlin to this map.
Its adjunct is RV-linear for gamma, because the adjunct of c.hom is gamma (hc):
the hom-equivalence formula gives gamma = ar.unit.app RV followed by pushforward
of c.hom. Thus direct image followed by scalar restriction is exactly pushforward
along gamma. Restrict the abelian hom equivalence to these linear morphisms.
Faithfulness makes the lifts unique; naturality gives the module adjunction am.
The identity underlying t proves the comparison equation, and the restricted
hom equivalence gives the final displayed equation.
(blueprint: lem-weil-pbc-etale-module-ring-iso-adjunction). -/
theorem etaleModuleRingIsoAdjunction (U V : Scheme.{u}) (f : U ⟶ V)
    (RV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    (RU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
    (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤ Sheaf U.smallEtaleTopology
      CommRingCat.{u + 1})
      (ar : Lr ⊣ (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale))
      (gamma : RV ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale)).obj RU) (c : Lr.obj RV ≅ RU)
    (hc :
      ar.homEquiv RV RU c.hom = gamma)
    (L0 : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
      1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)))
    (e0 : L0 ⋙ SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)) ≅ SheafOfModules.toSheaf
        ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
        ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f)
    (hlin : ∀ (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)) (F : SheafOfModules.{u + 1}
        ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)))
          (alpha : (Etale.upperStar AddCommGrpCat.{u + 1} f).obj ((SheafOfModules.toSheaf
        ((sheafCompose V.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj G) ⟶
        (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV))).obj F),
        (∃ h : L0.obj G ⟶ F, (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV))).map h = e0.hom.app G
        ≫ alpha) ↔
          ∃ k : G ⟶ (SheafOfModules.pushforward
        (J := V.smallGrothendieckTopology @Etale)
        (K := U.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f)
        ((sheafCompose V.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (ar.unit.app RV))).obj F,
        (SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).map k =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
        ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj G)
        ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV))).obj F) alpha) :
    ∃ (LM : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
      (e : LM ⋙ SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u
        + 1} RingCat.{u + 1})).obj RU) ≅ SheafOfModules.toSheaf ((sheafCompose
        V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV) ⋙
        Etale.upperStar AddCommGrpCat.{u + 1} f)
      (t : LM ⋙ SheafOfModules.pushforward (F := 𝟭 U.Etale) ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom ≅ L0)
      (am : LM ⊣ SheafOfModules.pushforward (J := V.smallGrothendieckTopology @Etale) (K :=
        U.smallGrothendieckTopology @Etale) (F := MorphismProperty.Over.pullback @Etale ⊤ f)
        ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        gamma)),
    (∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RV),
      (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj (Lr.obj RV))).map (t.hom.app G) ≫ e0.hom.app G = e.hom.app G) ∧
    (∀ (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
      1} RingCat.{u + 1})).obj RV)) (F : SheafOfModules.{u + 1} ((sheafCompose
      U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
      (h : LM.obj G ⟶ F),
      (SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj RV)).map (am.homEquiv G F h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
          ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
          1} RingCat.{u + 1})).obj RV)).obj G)
          ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RU)).obj F)
          (e.inv.app G ≫ (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂
            CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)).map h)) := by sorry

end AlgebraicGeometry
