/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BaseChangeShiftAuxComparison
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # Composition of the constant coefficient pullbacks

Source: blueprint latest, relative Kummer proof, Step 3, punctured square
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).

The canonical pullbacks of the constant coefficients are compatible with composition, both
before and after derivation. Consequently, for a commutative square the derived constant
pullbacks along the two paths agree through the square comparison of derived pullbacks.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The canonical pullbacks on constants are compatible with composition.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer).
Proof: the site comparison identifications and the constant-sheaf identifications are each
compatible with composition. -/
theorem constantPullback_comp (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ProEtale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app (P.constant Z) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).map (P.constantPullback g) ≫
        P.constantPullback f = P.constantPullback (f ≫ g) := by
  have hs := ProEtale.comparisonUpperStarCompUpperStarIso_inv_comp
    (ModuleCat.{u + 1} P.Coefficient) f g (P.constantEtale Z)
  have hh : (ProEtale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).obj
          (P.constantEtale Z)) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).map
        ((ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient)
          g).hom.app (P.constantEtale Z)) ≫
        (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient)
          f).hom.app ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).obj
            (P.constantEtale Z)) =
      (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient)
        (f ≫ g)).hom.app (P.constantEtale Z) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
            (P.constantEtale Z)) := by
    rw [← cancel_epi ((ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) (f ≫ g)).inv.app (P.constantEtale Z)),
      ← reassoc_of% hs, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  have hn := (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient)
    f).hom.naturality ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient)
      g).hom.app (ModuleCat.of P.Coefficient P.Coefficient))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  unfold constantPullback
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn, reassoc_of% hh]
  rw [← Functor.map_comp, ← Functor.map_comp]
  erw [Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} P.Coefficient) f g
    (ModuleCat.of P.Coefficient P.Coefficient)]

/-- The derived constant coefficient pullbacks are compatible with composition.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer).
Proof: the single-degree comparisons are compatible with the composition isomorphisms; then
apply `constantPullback_comp`. -/
theorem derivedCoefficientPullback_comp_false (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
        (P.derivedSheaf h Z false) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
        (P.derivedCoefficientPullback h g false) ≫
        P.derivedCoefficientPullback h f false =
      P.derivedCoefficientPullback h (f ≫ g) false := by
  have hc := ProEtale.leftDerivedUpperStarComp_hom_app_singleFunctor
    (ModuleCat.{u + 1} P.Coefficient) f g (P.constant Z)
  have hn := (ProEtale.singleFunctorCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.naturality
    (P.constantPullback g)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  unfold derivedCoefficientPullback
  dsimp only
  rw [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn, reassoc_of% hc]
  rw [← Functor.map_comp, ← Functor.map_comp, constantPullback_comp]
  rfl

/-- Transport of the derived coefficient pullback along an equality of morphisms.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
theorem leftDerivedUpperStarCongr_derivedCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f')
    (twisted : Bool) :
    (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) e).hom.app
        (P.derivedSheaf h Y twisted) ≫ P.derivedCoefficientPullback h f' twisted =
      P.derivedCoefficientPullback h f twisted := by
  subst e
  simp

/-- The derived constant pullbacks along the two paths of a commutative square agree through
the square comparison of derived pullbacks.
Source: blueprint relative Kummer proof, Step 3, punctured square
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
Proof: expand the square comparison into the two composition isomorphisms and the transport
along the equality of composites; apply `derivedCoefficientPullback_comp_false` twice. -/
theorem leftDerivedUpperStarSquareIso_derivedCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X}
    {π' : X' ⟶ Y'} {π : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq u' π' π g) :
    (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} P.Coefficient) sq).hom.app
        (P.derivedSheaf h Y false) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.map
        (P.derivedCoefficientPullback h π false) ≫
        P.derivedCoefficientPullback h u' false =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) π').leftDerivedFunctor.map
        (P.derivedCoefficientPullback h g false) ≫
        P.derivedCoefficientPullback h π' false := by
  dsimp only [ProEtale.leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, P.derivedCoefficientPullback_comp_false h u' π,
    P.leftDerivedUpperStarCongr_derivedCoefficientPullback h,
    ← P.derivedCoefficientPullback_comp_false h π' g, Iso.inv_hom_id_app_assoc]

end WeilConjectures.PurityFiniteSetting
