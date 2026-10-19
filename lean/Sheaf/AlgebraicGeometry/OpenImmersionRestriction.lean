/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Sheaf.AlgebraicGeometry.LerayBounded

import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.AlgebraicGeometry.RGammaUnboundedBounded
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Restriction and Leray for an open immersion

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`, node
`lem-kun-open-immersion-restriction`; Stacks Project, Tags 08BJ, 070K, 070Y and 070I
(blueprint: lem-kun-open-immersion-restriction).

The canonical unbounded Leray map is the hom component of
`rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`. The final equality says that
its restriction to the bounded-below derived category is the inverse of
`rightDerivedGlobalSectionsLerayPlus`, under `rightDerivedFunctorPlusCompatibility`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The counit of inverse image followed by direct image along an open immersion is a
natural isomorphism. The canonical Leray map is invertible for every unbounded derived
abelian sheaf, and restricts to the inverse of the bounded-below Leray isomorphism.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`, node
`lem-kun-open-immersion-restriction`; Stacks Project, Tags 08BJ, 070K, 070Y and 070I
(blueprint: lem-kun-open-immersion-restriction).

Proof:
1. The direct image is fully faithful by
   `lem-sc-open-immersion-pushforward-fully-faithful`. For the adjunction of
   `def-weil-pbc-inverse-image`, this is equivalent to invertibility of its counit.
2. Represent F by a complex C and choose a K-injective resolution C → I using
   `prop-weil-pbc-kinjective-resolutions-exist` (with integer coefficients).
   Inverse image is additive and exact by `prop-weil-pbc-inverse-image-exact` and is
   left adjoint to direct image. Therefore `lem-weil-pbc-right-adjoint-preserves-kinjective`
   makes j_*I K-injective, with no boundedness or cohomological-dimension assumption.
3. Apply `lem-weil-pbc-kinjective-total-derived` to the termwise direct image and sections
   functors: additivity makes their homotopy functors exact (they preserve shifts and
   cone matrices). Then Rj_*F is computed by j_*I, and `def-kun-rgamma-unbounded`
   computes the two sections objects by Γ(X,j_*I) and Γ(U,I). In degree r the former
   is I^r(X ×_X U). The projection X ×_X U → U is an isomorphism with inverse
   (j,id), by `def-pc-fibre-product`. Restriction along this inverse gives the
   degreewise comparison. Naturality in I^r makes it a chain isomorphism.
4. By `lem-weil-pbc-kinjective-hom-derived`, a derived morphism lifts uniquely up to
   homotopy between K-injective representatives. Its restriction squares commute
   degreewise. Additive sections and direct image preserve homotopies, proving naturality
   and independence of the resolution. For bounded-below F use the bounded-below
   injective representative of `lem-weil-pbc-dplus-injective-representative`.
   `lem-kun-rgamma-unbounded-bounded` identifies its sections with the unbounded recipe.
   The map of `lem-kun-leray-bdd` uses the same chain isomorphism in the opposite
   direction. The standard bounded/unbounded comparison isomorphisms therefore give
   exactly the commuting square below. -/
theorem openImmersion_restriction_leray {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).counit ∧
    (∀ F : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{u + 1} j).hom.app F)) ∧
    (∀ E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}),
      DerivedCategory.Plus.ι.map (rightDerivedGlobalSectionsLerayPlus j E).inv ≫
          (Sheaf.Γ U.smallEtaleTopology
            AddCommGrpCat.{u + 1}).rightDerivedFunctorPlusCompatibility.hom.app E =
        (Sheaf.Γ X.smallEtaleTopology
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlusCompatibility.hom.app
              ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlus.obj E) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
            ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlusCompatibility.hom.app E) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{u + 1} j).hom.app (DerivedCategory.Plus.ι.obj E)) := by
  sorry

end AlgebraicGeometry.Etale
