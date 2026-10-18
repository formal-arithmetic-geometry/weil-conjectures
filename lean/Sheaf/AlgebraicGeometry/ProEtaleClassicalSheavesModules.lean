/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules

import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Classical pro-étale sheaves of modules

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
`sk-thm-pe-classical-sheaves-modules`; Stacks Project, Tags 099T, 04JC and 03DA
(blueprint: det-pe-classical-sheaves-modules).

We use the fixed-coefficient `ModuleCat` encoding explicitly allowed by
`def-weil-pbc-etale-sheaves`. The constant-ring action is the unique extension of
its discrete scalar actions through sheafification; comparison carries those scalar
actions along the same inclusion of sites. Classicality is the existing predicate
on the underlying sheaf of sets, as in clause 3 of the continuity-map node.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Comparison inverse image is exact and fully faithful on modules over any discrete
commutative ring, with essential image the classical module sheaves and restriction
as quasi-inverse.
Source: Weil conjectures blueprint, main-20261015,
`sk-thm-pe-classical-sheaves-modules`; Stacks Project, Tags 099T, 04JC and 03DA
(blueprint: det-pe-classical-sheaves-modules).

Proof, following the five steps of the node:
1. Use the set adjunction of def-weil-pbc-site-comparison-morphism. Transport addition,
   zero, negation and scalar action through its finite-product comparisons. Functoriality
   preserves the module identities. Restriction carries the same actions back, with
   coefficients restricted along the unit on the constant ring, which is invertible by
   det-pe-classical-sheaves-unit. Naturality with all these operations, together with
   the coefficient triangle identity, makes the unit and counit linear. Consequently
   the mutually inverse adjunct maps restrict to linear maps and give the module
   adjunction. In the fixed-coefficient encoding these are comparisonUpperStar and
   comparisonLowerStar, defined by Kan extension and sheafification, and restriction.
2. Apply lem-weil-pbc-site-pullback-abelian-exact on larger-universe small site models.
   By lem-weil-pbc-module-sheaves-colimits-forgetful, kernels are sectionwise and
   cokernels are sheafified sectionwise cokernels in both module and abelian sheaves.
   The abelian kernel and cokernel comparisons are linear, since induced by the linear
   inclusions and quotients; their inverses are linear locally. Transported addition
   gives additivity. Thus the module functor preserves finite limits and finite colimits,
   with no finite-ring hypothesis. These are its exactness clauses.
3. By det-pe-classical-sheaves-unit every map between inverse-image underlying sheaves
   lifts uniquely. If the given map is linear, faithfulness reflects its addition, zero
   and scalar compatibility equations, including on the product domains. The lift is
   therefore linear. Conversely step 1 preserves linearity. This gives the displayed
   bijection on module Hom sets.
4. In a filtered module colimit each element is represented by a stage element; add
   after passing to a common later stage and act on a representative by its scalar.
   Eventual equality makes these operations well defined. Thus the underlying set is
   the filtered set colimit, and the linear continuity map has the same underlying map.
   A bijective linear map has a linear inverse. Hence module classicality is exactly
   IsClassical on the underlying set sheaf, using det-pe-classical-definition-continuity-map.
5. Apply det-pe-classical-sheaves-image on underlying set sheaves. Inverse images are
   classical and the counit is invertible precisely on classical objects. Steps 1 and 4
   make the counit and its inverse linear. The unit is linear and invertible by
   det-pe-classical-sheaves-unit. The unchanged triangle identities give the equivalence
   with restriction as quasi-inverse. The last two clauses record its counit and
   essential-image characterizations, respectively. -/
theorem proEtaleClassicalSheavesModules (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ (adj :
        comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⊣
          comparisonLowerStar (ModuleCat.{u + 1} Λ) X),
      PreservesFiniteLimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) ∧
      PreservesFiniteColimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) ∧
      (∀ F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
        Function.Bijective (fun f : F ⟶ G ↦
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map f)) ∧
      (∀ G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ),
        IsClassical ((sheafCompose (Scheme.ProEt.topology X)
          (forget (ModuleCat.{u + 1} Λ))).obj G) ↔
          IsIso (adj.counit.app G)) ∧
      (∀ G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ),
        IsClassical ((sheafCompose (Scheme.ProEt.topology X)
          (forget (ModuleCat.{u + 1} Λ))).obj G) ↔
          ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
            Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F ≅ G)) := by
  sorry

end AlgebraicGeometry.ProEtale
