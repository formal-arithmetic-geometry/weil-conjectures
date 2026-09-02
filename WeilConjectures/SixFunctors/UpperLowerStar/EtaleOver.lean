/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!
# Pullback of étale sheaves, constant sheaves and the localized small étale site

For a morphism of schemes `f : X ⟶ Y` the pullback `f^*` of étale sheaves commutes with the
constant sheaf functors (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`), since base
change preserves the terminal object of the small étale site; in particular the pullback of
a constant sheaf is constant (`AlgebraicGeometry.Scheme.isConstant_upperStar`).

For an étale `X`-scheme `U`, the restriction of a sheaf `F` to the small étale site of `X`
localized at `U` is, through the equivalence of sites
`AlgebraicGeometry.Scheme.Etale.overSheafEquiv`, the pullback of `F` along `U.hom`
(`AlgebraicGeometry.Scheme.Etale.overSheafEquivIso`): both are restriction along the
localization functor, which computes `U.hom^*` by
`AlgebraicGeometry.Scheme.GrothendieckTopology.upperStarIsoLocalizationRestriction`. Hence
the restriction of `F` to the localized site is constant if and only if `U.hom^* F` is
(`AlgebraicGeometry.Scheme.isConstant_over_iff_upperStar`).
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

/-- The pullback of étale sheaves along `f : X ⟶ Y` sends constant sheaves to constant
sheaves: `constantSheaf ⋙ f^*` and `constantSheaf` are both left adjoint to global
sections of the pushforward, since base change preserves the terminal object of the
small étale site (`X ×_Y Y ≅ X`):

```
                constantSheaf Y.smallEtaleTopology A
         A ──────────────────────────────────────────→ Sheaf Y.smallEtaleTopology A
          \                                                       │
           \ constantSheaf X.smallEtaleTopology A                  │ f^*
            ↘                                                      ↓
                                                        Sheaf X.smallEtaleTopology A
```
-/
def upperStarConstantSheafIso (f : X ⟶ Y) :
    constantSheaf Y.smallEtaleTopology A ⋙ Etale.upperStar A f ≅
      constantSheaf X.smallEtaleTopology A :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal).comp
        (Etale.upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (NatIso.ofComponents
        (F := Etale.lowerStar A f ⋙
          (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)))
        (G := (sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale)))
        (fun H ↦ H.obj.mapIso (PreservesTerminal.iso f.Etale).op.symm)
        (fun α ↦ (α.hom.naturality _).symm)))
    (constantSheafAdj X.smallEtaleTopology A terminalIsTerminal)

/-- **The pullback of a constant sheaf is constant.** -/
lemma isConstant_upperStar (g : Y ⟶ X) (F : Sheaf X.smallEtaleTopology A)
    [F.IsConstant X.smallEtaleTopology] :
    ((Etale.upperStar A g).obj F).IsConstant Y.smallEtaleTopology := by
  obtain ⟨a, ⟨i⟩⟩ := F.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    ((Etale.upperStar A g).mapIso i.symm ≪≫ (upperStarConstantSheafIso A g).app a)

variable (U : X.Etale)

set_option backward.isDefEq.respectTransparency false in
/-- **The restriction of a sheaf to the small étale site localized at `U`, transported to
the small étale site of `U.left`, is the pullback along `U.hom`.** Both are restriction
along the localization functor `U.left.Etale ⥤ X.Etale`:

```
                              overPullback A U
  Sheaf X.smallEtaleTopology A ────────────→ Sheaf (X.smallEtaleTopology.over U) A
                     \                                        │
                      \ U.hom^*                                │ (overSheafEquiv A U).functor
                       ↘                                       ↓
                                          Sheaf U.left.smallEtaleTopology A
```
-/
def Etale.overSheafEquivIso :
    X.smallEtaleTopology.overPullback A U ⋙ (Etale.overSheafEquiv A U).functor ≅
      Etale.upperStar A U.hom :=
  (Functor.fullyFaithfulCancelRight (sheafToPresheaf U.left.smallEtaleTopology A)
      (NatIso.ofComponents
        (fun F ↦ Functor.isoWhiskerRight
          (NatIso.op (MorphismProperty.Over.overEquivInverseCompForgetIso U).symm) F.obj)
        (fun φ ↦ by ext V; exact (φ.hom.naturality _).symm)) :
      X.smallEtaleTopology.overPullback A U ⋙ (Etale.overSheafEquiv A U).functor ≅
        GrothendieckTopology.localizationRestriction A @AlgebraicGeometry.Etale
          @AlgebraicGeometry.Etale le_rfl U.hom U.prop) ≪≫
    (GrothendieckTopology.upperStarIsoLocalizationRestriction A @AlgebraicGeometry.Etale
      @AlgebraicGeometry.Etale le_rfl U.hom U.prop).symm

set_option backward.isDefEq.respectTransparency false in
/-- The restriction of `F` to the small étale site localized at an étale `X`-scheme `U` is
constant if and only if the pullback of `F` to `U.left` is constant. -/
lemma isConstant_over_iff_upperStar (F : Sheaf X.smallEtaleTopology A) :
    (F.over U).IsConstant (X.smallEtaleTopology.over U) ↔
      ((Etale.upperStar A U.hom).obj F).IsConstant U.left.smallEtaleTopology := by
  refine (Sheaf.isConstant_sheafCongr_functor_iff (J := X.smallEtaleTopology.over U)
      (K := U.left.smallEtaleTopology) (A := A) (Etale.overEquiv U) terminalIsTerminal
      (F.over U)).symm.trans ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · exact Sheaf.isConstant_congr (F := (Etale.overSheafEquiv A U).functor.obj (F.over U)) _
      ((Etale.overSheafEquivIso A U).app F)
  · exact Sheaf.isConstant_congr (G := (Etale.overSheafEquiv A U).functor.obj (F.over U)) _
      ((Etale.overSheafEquivIso A U).app F).symm

end AlgebraicGeometry.Scheme

end
