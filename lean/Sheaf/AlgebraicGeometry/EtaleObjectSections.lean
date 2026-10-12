/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.Paper.EtaleRestrictionPullbackUnit

/-! # Evaluation on an étale object and global sections

Source: Stacks Project, Tag 03S2.
(blueprint: lem-weil-pbc-etale-object-sections-base-change)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural evaluation/global-sections comparison for an étale object.
Source: Stacks Project, Tag 03S2.
(blueprint: lem-weil-pbc-etale-object-sections-base-change) -/
noncomputable def etaleObjectSectionsIso {X : Scheme.{u}} (V : X.Etale) :
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V) ≅
      upperStar AddCommGrpCat.{u + 1} V.hom ⋙
        Sheaf.Γ V.left.smallEtaleTopology AddCommGrpCat.{u + 1} := by
  let A := AddCommGrpCat.{u + 1}
  let w : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let eW : (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.hom)).obj w ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [w])
  exact (sheafSections X.smallEtaleTopology A).mapIso eW.op ≪≫
    Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction A V.hom inferInstance).symm
      ((sheafSections V.left.smallEtaleTopology A).obj (op w)) ≪≫
    Functor.isoWhiskerLeft (upperStar A V.hom)
      (Sheaf.ΓNatIsoSheafSections V.left.smallEtaleTopology A
        (MorphismProperty.Over.mkIdTerminal (P := @Etale) V.left)).symm

/-- Étale evaluation is compatible with the unit for an arbitrary base change.
Source: Stacks Project, Tags 03CF, 03EF and 03S2.
(blueprint: lem-weil-pbc-etale-object-sections-base-change)

Proof: Write p = Vf.hom and q = Vg.hom. The lift i = pullback.lift m q hm'
identifies Vg with Vf ×_Y X: its inverse is obtained by composing the projection to Vf
with Vf's projection to W and pairing that with the projection to X; the two identities
follow by pullback extensionality, hm, hm' and g = h ≫ f. Thus i is an isomorphism.
Apply etale_restriction_pullback_unit to (h,p,m,q) and i. In that equality the
restriction comparisons rhoH and rho(h^*H) are invertible. Move them to the other
sides and compose with global-sections/terminal-evaluation comparisons. Their inverses,
together with the identity-object isomorphisms eW and eW', are precisely the two
etaleObjectSectionsIso components in this statement. The map theta is the inverse of
the terminal-object pullback isomorphism used in globalSectionsUpperStarMap: both maps
have projections m and the identity, so pullback extensionality identifies them.
The composite of the h-unit on Vf with restriction along i is the W-component of the
f-pushforward of that unit followed by lowerStarComp; this follows from its definition
by the canonical pullback-pasting isomorphism and uniqueness of the two projections.
Finally, naturality of terminal evaluation moves the comparison
(upperStarComp m p)^{-1} followed by upperStarComp q h past evaluation, giving exactly
the final Γ-map displayed here. No property of H or of h is used.
-/
theorem etaleObjectSections_baseChange {R X Y : Scheme.{u}} (W : R.Etale)
    (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R) (w : g = h ≫ f)
    (m : pullback W.hom g ⟶ pullback W.hom f)
    (hm : m ≫ pullback.fst W.hom f = pullback.fst W.hom g)
    (hm' : m ≫ pullback.snd W.hom f = pullback.snd W.hom g ≫ h)
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let A := AddCommGrpCat.{u + 1}
    let Vf := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
    let Vg := (MorphismProperty.Over.pullback @Etale ⊤ g).obj W
    (((lowerStar A f).map ((upperStarLowerStarAdjunction A h).unit.app H) ≫
        (lowerStarComp A h f g w).hom.app _).hom.app (op W)) ≫
        (etaleObjectSectionsIso Vg).hom.app ((upperStar A h).obj H) =
      (etaleObjectSectionsIso Vf).hom.app H ≫
        globalSectionsUpperStarMap A m ((upperStar A Vf.hom).obj H) ≫
        (Sheaf.Γ Vg.left.smallEtaleTopology A).map
          ((upperStarComp A m Vf.hom (m ≫ Vf.hom) rfl).inv.app H ≫
            (upperStarComp A Vg.hom h (m ≫ Vf.hom) hm').hom.app H) := by sorry


end AlgebraicGeometry.Etale
