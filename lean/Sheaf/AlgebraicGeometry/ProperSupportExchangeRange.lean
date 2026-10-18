/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.ProperSupportSectionCalculus
public import WeilConjectures.SixFunctors.BaseChange.Square
import Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-! # The image of the ordinary exchange on proper-support sections

Source: Stacks Project, Tags 0F55 and 0F76
(blueprint: lem-cbc-proper-support-exchange-range).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The ordinary exchange, restricted to the inverse image of the proper-support
subsheaf, is injective and has exactly the proper-support sections as image.

Source: Stacks Project, Tags 0F55 and 0F76.
(blueprint: lem-cbc-proper-support-exchange-range)

Proof:
Pullback of a section pulls its support back, so properness survives base change.
This defines a map G -> b_*H, for G = f_! F and H = f'_! a^*F. Adjunction gives
beta : b^*G -> H. Naturality of the adjunction identifies its composite with H's
inclusion with the restricted ordinary comparison. At an algebraically closed
geometric point, properSupport_geometricStalk identifies both support stalks with
properly supported sections on the same geometric fibre. Inverse-image stalk/germ
compatibility and the Cartesian fibre identification identify beta with the identity
on these sections. It is thus a stalk isomorphism. These geometric points cover the
base, so stalk detection makes beta an isomorphism of sheaves of modules. Composing
this isomorphism with the literal support inclusion gives the stated injectivity and
image equality on every etale object. -/
theorem properSupportExchange_range (Λ : Type (u + 1)) [CommRing Λ]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (a : X' ⟶ X)
    (b : Y' ⟶ Y) (f' : X' ⟶ Y') [IsSeparated f] [LocallyOfFiniteType f]
    [IsSeparated f'] [LocallyOfFiniteType f'] (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y'.Etale) :
    Function.Injective
      (((upperStar (ModuleCat.{u + 1} Λ) b).map
          ((properSupportLowerStarInclusion Λ f).app F) ≫
        (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F).hom.app (op V)) ∧
    ∀ s, (∃ t,
      (((upperStar (ModuleCat.{u + 1} Λ) b).map
          ((properSupportLowerStarInclusion Λ f).app F) ≫
        (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F).hom.app (op V)) t = s) ↔
      SectionHasProperSupport Λ ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)
        (f'.Etale.obj V) (pullback.fst V.hom f') s := by
  sorry

end AlgebraicGeometry.Etale
