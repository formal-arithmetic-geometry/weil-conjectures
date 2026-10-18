/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeArrowLocalization

/-!
# Canonical derived étale-localization comparisons

Source: Stacks Project, Étale Cohomology, Tag 0EZR, and Cohomology on Sites,
Tags 0D6G and 07A7 (blueprint: def-sbc-derived-localization-comparison-data).

The comparisons are actual natural transformations constructed from the canonical
inverse-image comparison and its derived adjunction mate. Their invertibility and
compatibility with the base-change arrow are stated in the consuming theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.BaseChangeLocalization

/-- Apply the canonical inverse-image square isomorphism termwise and descend to
unbounded derived categories, using the canonical composition identifications.
Source: Stacks Tag 07A7 (blueprint: def-sbc-derived-localization-comparison-data). -/
noncomputable def derivedInverseImageSquare
    {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : CommSq h e f g) :
    D((f)^*[AddCommGrpCat.{u + 1}]) ⋙ D((h)^*[AddCommGrpCat.{u + 1}]) ≅
      D((g)^*[AddCommGrpCat.{u + 1}]) ⋙ D((e)^*[AddCommGrpCat.{u + 1}]) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (squareUpperStarIso AddCommGrpCat.{u + 1} sq).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The canonical derived restriction/direct-image comparison is the mate of the
termwise inverse-image square. For a Cartesian square and étale `a`, it is the
slice-localization comparison of Tag 0D6G. No arbitrary isomorphism is chosen.
Source: Stacks Tags 07A7 and 0D6G
(blueprint: def-sbc-derived-localization-comparison-data). -/
noncomputable def derivedSliceComparison
    {X Y U V : Scheme.{u}}
    {h : Y ⟶ X} {a : U ⟶ X} {d : V ⟶ Y} {hU : V ⟶ U}
    (sq : CommSq d hU h a) :
    R((h)_*[AddCommGrpCat.{u + 1}]) ⋙ D((a)^*[AddCommGrpCat.{u + 1}]) ⟶
      D((d)^*[AddCommGrpCat.{u + 1}]) ⋙ R((hU)_*[AddCommGrpCat.{u + 1}]) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h)
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} hU)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquare sq).inv)).natTrans

variable {X Y S T U B : Scheme.{u}}
variable {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
variable (sq : ChosenCartesianSquare h e f g)
variable (a : U ⟶ X) (b : B ⟶ S) [Etale a] [Etale b]
variable (fU : U ⟶ B) (fac : a ≫ f = fU ≫ b)

/-- The canonical source comparison `C_L^D`: first compose inverse images for
`fa = bf_U`, then use the derived slice comparison for `g` localized at `B`.
Source: Stacks Tags 0EZR, 0D6G and 07A7
(blueprint: def-sbc-derived-localization-comparison-data). -/
noncomputable def derivedLeftComparison :
    R((g)_*[AddCommGrpCat.{u + 1}]) ⋙ D((f)^*[AddCommGrpCat.{u + 1}]) ⋙
        D((a)^*[AddCommGrpCat.{u + 1}]) ⟶
      D((pullback.snd b g)^*[AddCommGrpCat.{u + 1}]) ⋙
        R((pullback.fst b g)_*[AddCommGrpCat.{u + 1}]) ⋙
        D((fU)^*[AddCommGrpCat.{u + 1}]) :=
  Functor.whiskerLeft R((g)_*[AddCommGrpCat.{u + 1}])
      (derivedInverseImageSquare (CommSq.mk fac)).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedSliceComparison (IsPullback.of_hasPullback b g).flip.toCommSq)
      D((fU)^*[AddCommGrpCat.{u + 1}]) ≫
    (Functor.associator _ _ _).hom

/-- The canonical target comparison `C_R^D`: use the derived slice comparison for
`h` localized at `U`, then compose inverse images for `ed = ce_U`.
Source: Stacks Tags 0EZR, 0D6G and 07A7
(blueprint: def-sbc-derived-localization-comparison-data). -/
noncomputable def derivedRightComparison :
    D((e)^*[AddCommGrpCat.{u + 1}]) ⋙ R((h)_*[AddCommGrpCat.{u + 1}]) ⋙
        D((a)^*[AddCommGrpCat.{u + 1}]) ⟶
      D((pullback.snd b g)^*[AddCommGrpCat.{u + 1}]) ⋙
        D((localArrow sq a b fU fac)^*[AddCommGrpCat.{u + 1}]) ⋙
        R((pullback.fst a h)_*[AddCommGrpCat.{u + 1}]) :=
  Functor.whiskerLeft D((e)^*[AddCommGrpCat.{u + 1}])
      (derivedSliceComparison (IsPullback.of_hasPullback a h).flip.toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedInverseImageSquare
        (CommSq.mk (pullback.lift_snd (pullback.fst a h ≫ fU)
          (pullback.snd a h ≫ e) _).symm)).hom
      R((pullback.fst a h)_*[AddCommGrpCat.{u + 1}]) ≫
    (Functor.associator _ _ _).hom

end AlgebraicGeometry.Etale.BaseChangeLocalization
