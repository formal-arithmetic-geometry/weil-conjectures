/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction

/-!
# Cohomology pullback and the derived unit

Source: Stacks Project, cohomology.tex, Lemmas 01EZ and 01F8, equations 01F9 and 01FA;
sites-cohomology.tex, Remark 08J6 and Lemmas 072Z and 07A6
(blueprint: lem-weil-pbc-cohomology-pullback-derived-unit).

The Leray isomorphism used below is `Functor.rightDerivedFunctorPlusCompIso'` applied to
`Etale.lowerStarCompGlobalSectionsIso`. Its type is a natural isomorphism on all of D⁺.
`Sheaf.Γ` and its bounded below right derived functor are the recorded global-sections
functors; their comparison with the unbounded version is canonical.

The pullback `u^* : RΓ(X, K) ⟶ RΓ(Y, u⁻¹K)` on D⁺ of def-weil-pbc-cohomology-pullback (whose
recorded declaration `Etale.cohomologyMap` covers only the sheaf case) is spelled inline as the
derived comparison (`Functor.rightDerivedDesc`) of the section map `Γ(X, I) ⟶ Γ(Y, u⁻¹I)` given
by the underived unit, followed by the unit of `RΓ(Y, -)`: on resolutions `I` and `u⁻¹I → J`
it is the class of `a ↦ r(η(a))`.
-/

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A bounded below K-injective complex remains K-injective under direct image.
Source: Stacks Project, Lemma 08BJ and Remark 08J6
(blueprint: lem-weil-pbc-cohomology-pullback-derived-unit).
Proof, step 3 of the node: inverse image is exact and left adjoint to direct image.
For every acyclic complex `M`, maps `M → f_*J` up to homotopy correspond to maps
`f⁻¹M → J`, which vanish since `f⁻¹M` is acyclic and `J` is K-injective.
Boundedness is preserved because the additive direct image preserves zero objects. -/
theorem lowerStar_isKInjective_boundedBelow {X Y : Scheme.{v}} (f : Y ⟶ X)
    (J : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    [J.obj.IsKInjective] :
    ((lowerStar AddCommGrpCat.{v + 1} f).mapCochainComplexPlus.obj J).obj.IsKInjective := by
  sorry

/-- On a bounded below K-injective complex `J` the derived direct image and the derived global
sections on both sites are computed by `J` itself: the units are isomorphisms, so the natural
Leray isomorphism `Functor.rightDerivedFunctorPlusCompIso'`, characterized by its unit
compatibility `Functor.rightDerivedFunctorPlusCompIso'_fac`, is the sectionwise identification.
Source: Stacks Project, Lemma 01EZ and Remark 08J6
(blueprint: lem-weil-pbc-cohomology-pullback-derived-unit).
Proof, steps 1--5 of the node: derive the additive functors Γ and direct image. Maps between
K-injective representatives lift uniquely up to homotopy. Comparing a representative with a
chosen resolution gives a homotopy equivalence, so applying either additive functor gives
an isomorphism and the comparison commutes with every lifted map (step 2, using
lem-weil-pbc-kinjective-hom-derived and lem-weil-pbc-cohomology-pullback-functorial).
Direct image preserves K-injectives by step 3. On complexes the natural isomorphism
`f_* ⋙ Γ_X ≅ Γ_Y` is evaluation at the final object: `J(X ×_X Y) ≅ J(Y)`, including the
identification of differentials. Compose its localization with the two resolution
comparisons to obtain λ (step 4); the same comparison calculation makes it independent
of the representative. Sectionwise naturality and the lifted-map comparison give naturality
in every morphism of D⁺ (step 5, lem-weil-pbc-derived-direct-image-triangulated). -/
theorem lerayPlus_on_kInjective {X Y : Scheme.{v}} (f : Y ⟶ X)
    (J : HomotopyCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    [CochainComplex.IsKInjective J.obj.as] :
    IsIso ((lowerStar AddCommGrpCat.{v + 1} f).rightDerivedFunctorPlusUnit.app J) ∧
    IsIso ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusUnit.app
      ((lowerStar AddCommGrpCat.{v + 1} f).mapHomotopyCategoryPlus.obj J)) ∧
    IsIso ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusUnit.app
      J) := by
  sorry

/-- Pullback of derived global sections is Γ of the derived unit followed by the natural
Leray identification, for every bounded below derived object (including a sheaf in degree 0).
Source: Stacks Project, Lemma 01F8 and equations 01F9 and 01FA
(blueprint: lem-weil-pbc-cohomology-pullback-derived-unit).
Proof, steps 6--7 of the node: represent `K` by a bounded below complex, resolve it by `I`,
and resolve its inverse image by `J`. Property (2) of
prop-weil-pbc-derived-inverse-image-adjunction represents the derived unit by the underived
unit followed by direct image of the comparison into `J`. Naturality of the underived unit
replaces this by `I → f_*f⁻¹I → f_*J` after the resolution map. The lifted-map comparison
of step 2 computes Γ of this derived map on `I` and `f_*J`. The Leray comparison of step 4
then identifies it, section by section, with `a ↦ r(η(a))`, precisely the resolution
construction of def-weil-pbc-cohomology-pullback. Its canonical identifications are those
of lem-weil-pbc-cohomology-pullback-functorial (1), so the equality holds in D⁺. -/
theorem derivedCohomologyPullback_eq_derivedUnit {X Y : Scheme.{v}} (f : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})) :
    (Functor.rightDerivedDesc _
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso _)
      ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlus)
      (Functor.whiskerRight
          (NatTrans.mapHomotopyCategoryPlus
            ((Functor.leftUnitor _).inv ≫
              Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit
                (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
              (Functor.associator _ _ _).hom ≫
              Functor.whiskerLeft (upperStar AddCommGrpCat.{v + 1} f)
                (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f).hom))
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight
          (Functor.mapHomotopyCategoryPlusCompIso
            (Iso.refl (upperStar AddCommGrpCat.{v + 1} f ⋙
              Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}))).inv
          DerivedCategory.Plus.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar AddCommGrpCat.{v + 1} f).mapHomotopyCategoryPlus
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryPlusFactorsh.inv
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom)).app K =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorPlus.map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus.unit.app K) ≫
      (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (lowerStar AddCommGrpCat.{v + 1} f)
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}) _ _ _ _
        (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
          (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f))
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f)).hom.app
          ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryPlus.obj K) := by
  sorry

end AlgebraicGeometry.Etale
