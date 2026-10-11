/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction
import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# Strict-henselization stalk formula for the multiplicative sheaf

Source: literature/stacks-project/etale-cohomology.tex, Theorem Tag 03Q9
(theorem-higher-direct-images), first assertion (blueprint:
lem-weil-pbc-gm-strict-henselization-stalk-formula).
-/

universe w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The higher-direct-image stalk formula for `𝔾ₘ`, together with the pullback identification.
The canonical restriction `ρ^q` is `r ≫ strictHenselizationCohomologyComparison` for the germ
restriction `r` of `R^q f_* 𝔾ₘ`, which is unique with its defining components
(`existsUnique_strictHenselizationStalkRestriction`).
Source: Stacks, Tag 03Q9, first assertion and its units identification
(blueprint: lem-weil-pbc-gm-strict-henselization-stalk-formula).
1. Apply `lem-weil-pbc-unrestricted-strict-henselization-stalk` to the qcqs morphism,
the abelian sheaf of units, and the geometric point. The canonical germ restriction
followed by the derived base-change mate and Leray is the comparison of Tag 03Q9.
2. Apply `lem-weil-pbc-gm-pullback-strict-henselization` to the first projection.
The canonical units map is an isomorphism because units commute with the affine-transition
limit of étale neighbourhoods. Applying cohomology to this map and composing with Step 1
gives the final canonical identification with cohomology of the units sheaf.
-/
theorem gm_strictHenselization_stalk_formula
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ S) (q : ℕ) :
    ∃ r : (Scheme.pointSmallEtale xbar).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{w + 1} f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj X.gmSheaf))) ⟶
        (Sheaf.Γ (Scheme.strictHenselizationScheme xbar).smallEtaleTopology
          AddCommGrpCat.{w + 1}).obj
          ((upperStar AddCommGrpCat.{w + 1} (Scheme.strictHenselizationStructuralMap xbar)).obj
            ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{w + 1} f).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj X.gmSheaf)))),
      IsStrictHenselizationStalkRestriction xbar
          ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{w + 1} f).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj X.gmSheaf))) r ∧
        IsIso (r ≫ strictHenselizationCohomologyComparison xbar f X.gmSheaf q) ∧
        IsIso (Scheme.upperStarGmSheafToGmSheaf
          (pullback.fst f (Scheme.strictHenselizationStructuralMap xbar))) ∧
        IsIso (r ≫ strictHenselizationCohomologyComparison xbar f X.gmSheaf q ≫
          (cohomology AddCommGrpCat.{w + 1}
            (pullback f (Scheme.strictHenselizationStructuralMap xbar)) (q : ℤ)).map
            (DerivedCategory.Plus.ι.map
              ((DerivedCategory.Plus.singleFunctor _ 0).map
                (Scheme.upperStarGmSheafToGmSheaf
                  (pullback.fst f (Scheme.strictHenselizationStructuralMap xbar)))))) := by
  sorry

end AlgebraicGeometry.Etale
