/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
public import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Injective representative computation of the derived exchange

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-injective-exchange-representative).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Compute the derived mate on the chosen injective representative, before sections.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph, with the
factorization `Adjunction.derivedPlus_mateEquiv_app_fac`.
(blueprint: lem-weil-pbc-injective-exchange-representative).

Proof: regard the injective complex as an object of the bounded-below homotopy
category. Lift q to its localization using the fully faithful inclusion of D⁺
into D. Apply the derived mate factorization and naturality in this lift of q.
The source direct-image unit is invertible on the injective complex; cancel it.
The definition of sourceInjectiveDirectImageIso identifies its inverse with this
cancelled unit, followed by localization comparisons. The exact pullback
factorization identifies the underived exchange with Q of its termwise map.
Finally the defining unit compatibility of rightDerivedFunctorPlusCompatibility
changes the target bounded-below unit into the unbounded unit. Naturality moves
q.inv to the last factor. No target unit is inverted, so neither injectivity of
the pulled-back complex nor any acyclicity of it is required. -/
theorem injectiveExchange_representative {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M
    let T := P.mapDerivedCategoryPlus.obj K
    let a : (U.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj D :=
      (NatTrans.mapHomologicalComplex
      (baseChangeMap AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq)
      (.up ℤ)).app M
    U.mapDerivedCategoryFactors.inv.app L ≫
      U.mapDerivedCategory.map (sourceInjectiveDirectImageIso f K J q).inv ≫
      DerivedCategory.Plus.ι.map
        ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
          (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
            (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
          (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
            (IsPullback.of_hasPullback f
              (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom)).natTrans.app K) =
    DerivedCategory.Q.map a ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D) ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      F.rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.inv.app M ≫ P.mapDerivedCategory.map q.inv) ≫
      F.rightDerivedFunctorPlusCompatibility.inv.app T := by sorry

end AlgebraicGeometry.Etale
