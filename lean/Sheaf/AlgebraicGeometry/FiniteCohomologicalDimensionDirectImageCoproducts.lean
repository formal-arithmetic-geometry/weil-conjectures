/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Finite cohomological dimension and coproducts of derived direct images

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-exc-direct-image-coproducts.md;
Stacks Project, Tags 0F11 and 07K7 (blueprint: lem-exc-direct-image-coproducts).
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Finite cohomological dimension makes qcqs direct image with finite commutative
coefficients preserve all set-indexed coproducts on the ordinary unbounded derived categories.
There is no boundedness or constructibility restriction, and the index type may be empty.
Preservation means that the canonical comparison induced by the coprojections is invertible.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-exc-direct-image-coproducts.md;
Stacks Project, Tag 0F11, proof of (1), and Tag 07K7
(blueprint: lem-exc-direct-image-coproducts).

Proof:
1. The module-sheaf categories are Grothendieck abelian
   (lem-weil-pbc-module-sheaves-grothendieck-abelian), hence have enough injectives
   (lem-sp-grothendieck-enough-injectives). Direct image is additive and left exact
   (lem-weil-pbc-module-direct-image-left-exact). A finite ring has positive characteristic,
   taking characteristic one for the zero ring, so its module sheaves are torsion.
   Express a sum as the filtered colimit of finite subsums, including the empty subsum.
   Exact faithful coefficient forgetting preserves these colimits
   (lem-weil-pbc-module-sheaves-colimits-forgetful). The natural invertible derived
   coefficient comparison (lem-weil-pbc-module-abelian-derived-direct-image-comparison)
   identifies higher images after forgetting. Its naturality identifies the comparison
   on every finite-subsum leg. Apply lemma-weil-pbc-direct-image-filtered-colimit.
   Finite sums of injective resolutions compute finite sums of higher images, since
   finite sums of injectives are injective. Thus every higher image commutes with sums.
   Exact faithful forgetting reflects invertibility. The degree-zero identification
   (lem-sp-derived-well-defined) gives the assertion for underived direct image as well.
2. Choose degreewise injective K-injective representatives I_s
   (lem-pur-kinjective-degreewise-existence). Their termwise sum L represents the derived
   coproduct (lem-kun-grothendieck-derived-coproducts), without a common lower bound.
3. Injective terms are acyclic (lem-weil-pbc-derived-functor-injective-vanishing).
   Step 1 makes the terms of L acyclic too. Apply
   lem-kun-finite-cd-acyclic-complex with the bound c: its natural derived comparison is
   invertible at I_s and L, and identifies derived coprojections with termwise images.
   Uniqueness of the total right derived functor identifies this with rightDerivedLowerStar.
4. Step 1 in degree zero gives an isomorphism from the termwise sum of u_* I_s to u_* L.
   Its restrictions are the images of the coprojections, so it commutes with differentials.
   Localize this complex isomorphism. The target version of
   lem-kun-grothendieck-derived-coproducts identifies its source as the derived coproduct.
   Naturality in Step 3 makes this exactly the canonical coproduct comparison, hence an
   isomorphism. The empty family uses zero complexes and the same zero-to-zero comparison. -/
theorem rightDerivedLowerStar_preservesCoproducts_of_finite_dimension
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (f : U ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    (c : ℕ)
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (p : ℕ),
      c < p → IsZero (((lowerStar (ModuleCat.{u + 1} A) f).rightDerived p).obj M)) :
    ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) f) := by
  sorry

end AlgebraicGeometry.Etale
