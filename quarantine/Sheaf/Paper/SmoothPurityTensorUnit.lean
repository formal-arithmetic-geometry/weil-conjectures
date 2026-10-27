/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.AffineDiagonalTateCoordinates

/-! # Unit evaluation of the exceptional tensor mate

Source: smooth-purity model paragraph and projection-purity-agreement normalization.
(blueprint: lem-pur-smooth-tensor-mate-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- At the coefficient unit, the canonical exceptional tensor mate is the unit
constraint. No smoothness, affine coordinates or orientation is involved.
Source: blueprint latest, smooth-purity model paragraph;
lem-pur-projection-purity-agreement, final canonical reassociations.
(blueprint: lem-pur-smooth-tensor-mate-unit).

Proof: first calculate on the ordinary etale site. The tensor mate is the adjunct
of inverse projection followed by the exceptional counit. At the tensor unit,
the projection map is the unit constraint. Its inverse cancels that constraint,
and the adjunction triangle leaves the left unitor of the exceptional image.
The symmetry in smoothPurityEtaleTheta changes the right unitor to this left
unitor. The ordinary coefficient-unit isomorphism is smoothPurityUnitIso.
Transport through the monoidal site comparison and its pullback constraint.
Naturality of the comparison unit cancels its inverse occurring in
diagonalDualizingComparison against its forward occurrence in smoothPurityTheta.
The remaining pullback-unit map is exactly the explicit composite below.
Thus the two displayed morphisms agree. The calculation applies to every
compactifiable morphism, including identity morphisms and empty schemes. -/
theorem smoothPurityTheta_unit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    let e :=
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory.mapIso
          (X := (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
              (Etale.ordinaryFiniteUnit P.Coefficient Y))
          (projectionUnitRaw P.Coefficient Y) ≪≫
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) f).symm.app _ ≪≫
        ProEtale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) f
    P.smoothPurityTheta f
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
            (Etale.ordinaryFiniteUnit P.Coefficient Y))
        (Etale.ordinaryFiniteUnit P.Coefficient Y) (Iso.refl _) =
      (((curriedTensor (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))).mapIso
            e).app (P.diagonalDualizing f) ≪≫
        λ_ (P.diagonalDualizing f)).hom := by sorry

end WeilConjectures.PurityFiniteSetting
