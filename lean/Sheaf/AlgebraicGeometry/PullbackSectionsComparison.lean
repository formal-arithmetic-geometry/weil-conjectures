/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.Paper.EtaleRestrictionPullbackUnit
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Sections on an étale object as global sections on its base change

Source: Stacks Project, Tags 03S2, 03CF and 03EF; naturality of restriction and pullback units.
(blueprint: lem-weil-pbc-pullback-sections-comparison)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation at an étale object, followed by restriction to its base change and the
inverse-image composition isomorphism. Source: Stacks Tags 03S2 and 00XZ.
(blueprint: lem-weil-pbc-pullback-sections-comparison) -/
noncomputable def pullbackSectionsEquiv {R X : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale) (f : X ⟶ R) :
    ((lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj G)).obj.obj (op W) ≃+
      (Sheaf.Γ (pullback W.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} (pullback.fst W.hom f ≫ W.hom)).obj G) := by
  let A := AddCommGrpCat.{u + 1}
  let V : X.Etale := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let p : V.left ⟶ X := V.hom
  let F := (upperStar A f).obj G
  let w : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let eW : (MorphismProperty.Over.map ⊤ (inferInstance : Etale p)).obj w ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [w, p])
  let e₁ : F.obj.obj (op V) ≅
      ((localizationRestriction A p inferInstance).obj F).obj.obj (op w) :=
    F.obj.mapIso eW.op
  let e₂ := ((upperStarIsoLocalizationRestriction A p inferInstance).app F).symm
  let e₃ := ((Sheaf.ΓNatIsoSheafSections V.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) V.left)).app
      ((upperStar A p).obj F)).symm
  exact Iso.addCommGroupIsoToAddEquiv
    (e₁ ≪≫ ((sheafSections V.left.smallEtaleTopology A).obj (op w)).mapIso e₂ ≪≫
      e₃ ≪≫ (Sheaf.Γ V.left.smallEtaleTopology A).mapIso
        ((upperStarComp A p f (pullback.fst W.hom f ≫ W.hom)
          pullback.condition).symm.app G))

/-- Evaluation of f_* f^* G at an étale object W identifies naturally with the global
sections of the pullback of G to W ×_R X. This is a comparison for a single cartesian
square, independent of any limit or compactness hypotheses.
Source: Stacks Project, Tags 03S2, 03CF and 03EF.
(blueprint: lem-weil-pbc-pullback-sections-comparison)

Proof: By the definition of direct image, the source is (f^* G)(W ×_R X). Restriction
along the étale second projection identifies this with Γ(W ×_R X, p^* f^* G), using the
étale inverse-image/restriction isomorphism and evaluation at the terminal object.
Compose with the inverse-image composition isomorphism and the equality
p ≫ f = fst ≫ W.hom to obtain the displayed additive equivalence. For a cartesian map m,
apply the restriction/pullback-unit identity to the square over h. Naturality of the
restriction isomorphism moves the composition isomorphism past restriction. Naturality
of the unit moves the source composition isomorphism past pullback. Associativity of
inverse-image composition identifies the resulting composites. The two projection
equations specify the canonical cartesian map, so this proves the stated equality for
any m satisfying them. Every map is additive, and hence the equivalences preserve zero. -/
theorem pullbackSections_comparison (R : Scheme.{u})
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale) :
    let A := AddCommGrpCat.{u + 1}
    let v := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ pullback.fst W.hom f ≫ W.hom
    let F := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ (upperStar A (v f)).obj G
    let e := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ pullbackSectionsEquiv G W f
      ∀ {X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R)
        (w : g = h ≫ f) (m : pullback W.hom g ⟶ pullback W.hom f)
        (hm : m ≫ pullback.fst W.hom f = pullback.fst W.hom g)
        (hm' : m ≫ pullback.snd W.hom f = pullback.snd W.hom g ≫ h)
        (s : ((lowerStar A f).obj ((upperStar A f).obj G)).obj.obj (op W)),
        e g (((lowerStar A f).map
            ((upperStarLowerStarAdjunction A h).unit.app ((upperStar A f).obj G)) ≫
          (lowerStarComp A h f g w).hom.app _ ≫
          (lowerStar A g).map ((upperStarComp A h f g w).inv.app G)).hom.app (op W) s) =
        (globalSectionsUpperStarMap A m (F f) ≫
          (Sheaf.Γ (pullback W.hom g).smallEtaleTopology A).map
            ((upperStarComp A m (v f) (v g)
              (by dsimp [v]; rw [← Category.assoc, hm])).inv.app G)) (e f s) := by
  sorry

end AlgebraicGeometry.Etale
