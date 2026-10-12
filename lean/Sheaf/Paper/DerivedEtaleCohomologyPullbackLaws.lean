/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Identity and composition of pullback on derived étale cohomology

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-derived-cohomology-pullback-laws).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborating the dependent presentation families and compatibility equations.
/-- Identity and composition of pullback on derived étale cohomology.
Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-derived-cohomology-pullback-laws).

Proof: Rewrite every P using hP. For the identity scheme map, the inverse-image
identity isomorphism identifies the adjunction unit with the identity after
the direct-image identity isomorphism. The Leray comparison for that direct
image is the same identity comparison. The complex identity map in the
statement is the inverse-image identity comparison, so all comparisons cancel.
For composable maps, naturality moves the second unit past the first lifted
complex morphism. The composite-unit equation for inverse images identifies
the two units with the unit of g ≫ f, transported through upperStarComp.
The derived direct-image composition is its conjugate under the adjunctions;
the Leray comparison is compatible with that composition by the uniqueness
of right-derived comparisons. The two complex comparison maps combine to
the displayed map of the composite pair, by naturality of
mapDerivedCategoryFactors and the composition comparison. Apply RΓ and
homologyFunctor, using preservation of composition, to obtain the equation.
These arguments apply to all cochain complexes; bounded-below complexes are
only the inputs needed in this statement. -/
theorem derivedEtaleCohomology_pullback_laws
    (P : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (_ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      (cohomology AddCommGrpCat.{uNatural + 1} X n).obj (DerivedCategory.Q.obj K) ⟶
        (cohomology AddCommGrpCat.{uNatural + 1} Y n).obj (DerivedCategory.Q.obj L))
    (hP : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      P f K L v n = (DerivedCategory.homologyFunctor AddCommGrpCat.{uNatural + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
            ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app
              (DerivedCategory.Q.obj K)) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{uNatural + 1} f).hom.app
              ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj
                (DerivedCategory.Q.obj K)) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Y).map
            ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map v))) :
    (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        ∀ n : ℤ, P (𝟙 X) K.obj K.obj
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{uNatural + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) n = 𝟙 _) ∧
      (∀ {X Y Z : Scheme.{uNatural}} (f : Y ⟶ X) (g : Z ⟶ Y)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (N : CochainComplex.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
        (w : ((upperStar AddCommGrpCat.{uNatural + 1} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj ⟶ N.obj),
        ∀ n : ℤ, P (g ≫ f) K.obj N.obj
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{uNatural + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{uNatural + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) n =
            P f K.obj L.obj v n ≫
              P g L.obj N.obj w n) := by
  sorry

end AlgebraicGeometry.Etale
