/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Geometric stalks of the extension-by-zero base-change mate

Source: Stacks Project, Etale Cohomology, Lemma 03S6 and Proposition 03S5;
Modules on Sites, Lemma 03DI (blueprint: lem-cbc-base-change-mate-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- The canonical base-change morphism has the inverse-image stalk map inside the open
and the unique map between zero objects outside it. The morphism is the inverse of
the existing canonical mate, written using `asIso` and its proved invertibility.
The transpose of that mate is
`gU^*` of the unit followed by `squareUpperStarIso`, as proved by
`Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app`.

The first equality transports the stalk of the canonical inverse from the stalk of `F`.
It uses the inverse-image identification for `gU`, the unit for `j`, the square comparison, and
the inverse-image identification for `j'`; its target is identified by the inside-open
stalk formula. It is exactly the inverse-image identification for `gU`.

Proof: first use the extension-by-zero stalk formulas and the inverse-image stalk
identification (lem-weil-pbc-extension-by-zero-stalks, lem-kun-stalk-as-pullback).
Inside the open, the unit sends a germ represented by a section to the same section in
the sheafification of the extension presheaf, and the inside-stalk formula sends it back
to that germ. The explicit adjunction formula of Lemma 03DI therefore makes the mate
the identity under these identifications. Its inverse is the displayed inverse-image
map. Outside the open, cartesianness puts the image point outside the original open;
both stalks vanish, so the induced map is the unique zero map.
Source: Stacks Project, Lemma 03S6, Proposition 03S5, and Lemma 03DI
(blueprint: lem-cbc-base-change-mate-stalk). -/
theorem Etale.openImmersionLowerShriekBaseChangeMate_stalk
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    (∀ (t : Spec (.of Ω) ⟶ U'),
      (upperStarCompUliftSheafFiberIso AddCommGrpCat.{u + 1} gU t).inv.app F ≫
        ((pointSmallEtale t).ulift.{u + 1}).sheafFiber.map
          ((upperStar AddCommGrpCat.{u + 1} gU).map
            ((@openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
              _ _ _ _ _ j sq.isOpenImmersion).unit.app F)) ≫
        ((pointSmallEtale t).ulift.{u + 1}).sheafFiber.map
          ((squareUpperStarIso AddCommGrpCat.{u + 1} sq.toCommSq.flip).hom.app
            ((@openImmersionLowerShriek AddCommGrpCat.{u + 1} _ _ _ _ _ j
              sq.isOpenImmersion).obj F)) ≫
        (upperStarCompUliftSheafFiberIso AddCommGrpCat.{u + 1} j' t).hom.app
          ((upperStar AddCommGrpCat.{u + 1} g).obj
            ((@openImmersionLowerShriek AddCommGrpCat.{u + 1} _ _ _ _ _ j
              sq.isOpenImmersion).obj F)) ≫
        ((pointSmallEtale (t ≫ j')).ulift.{u + 1}).sheafFiber.map ((@asIso _ _ _ _
          (@openImmersionLowerShriekBaseChangeMap AddCommGrpCat.{u + 1}
            _ _ _ U' U X' X gU j' j g sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq)
          (@isIso_openImmersionLowerShriekBaseChangeMap AddCommGrpCat.{u + 1}
            _ _ _ _ U' U X' X gU j' j g sq.isOpenImmersion sq.isOpenImmersion'
            (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
              sq.hom_fst sq.hom_snd))).inv.app F) ≫
        (@openImmersionLowerShriekCompUliftSheafFiberIso AddCommGrpCat.{u + 1}
          _ _ _ U' X' j' sq.isOpenImmersion' Ω _ _ t).hom.app
            ((upperStar AddCommGrpCat.{u + 1} gU).obj F) =
      (upperStarCompUliftSheafFiberIso AddCommGrpCat.{u + 1} gU t).inv.app F) ∧
    (∀ (s : Spec (.of Ω) ⟶ X'),
      s.base (IsLocalRing.closedPoint Ω) ∉ Set.range j'.base →
        IsZero (((pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj
          ((upperStar AddCommGrpCat.{u + 1} g).obj
            ((@openImmersionLowerShriek AddCommGrpCat.{u + 1} _ _ _ _ _ j
              sq.isOpenImmersion).obj F))) ∧
        IsZero (((pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj
          ((@openImmersionLowerShriek AddCommGrpCat.{u + 1} _ _ _ _ _ j'
            sq.isOpenImmersion').obj ((upperStar AddCommGrpCat.{u + 1} gU).obj F))) ∧
        ((pointSmallEtale s).ulift.{u + 1}).sheafFiber.map ((@asIso _ _ _ _
          (@openImmersionLowerShriekBaseChangeMap AddCommGrpCat.{u + 1}
            _ _ _ U' U X' X gU j' j g sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq)
          (@isIso_openImmersionLowerShriekBaseChangeMap AddCommGrpCat.{u + 1}
            _ _ _ _ U' U X' X gU j' j g sq.isOpenImmersion sq.isOpenImmersion'
            (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
              sq.hom_fst sq.hom_snd))).inv.app F) = 0) := by
  sorry

end AlgebraicGeometry
