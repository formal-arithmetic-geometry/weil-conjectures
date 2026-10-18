/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Direct sums and finite cohomological dimension

Source: the blueprint of the Weil conjectures, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary`, node `lem-kun-0f11`, order 1732; Stacks Project,
Etale Cohomology, Tag 0F11 (`lemma-finite-cd-mod-n-direct-sums`)
(blueprint: lem-kun-0f11).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- If `n ≥ 1` and `f` is quasi-compact, quasi-separated and of finite torsion étale
cohomological dimension, derived direct image on `ZMod n`-module étale sheaves commutes
with every set-indexed coproduct; for every qcqs scheme of finite torsion étale
cohomological dimension, derived global sections has the same property. The coefficient
ring is lifted by the canonical ring equivalence `ULift.ringEquiv` to the universe used
by the existing six-functor and derived-category interfaces.

Source: Stacks Project, Etale Cohomology, Tag 0F11, `lemma-finite-cd-mod-n-direct-sums`,
assertions (1) and (2) (blueprint: lem-kun-0f11).

Proof:
1. Put A = Z/nZ. Its module sheaves are torsion. The coefficient-forgetting
   comparison (lem-sbc-higher-direct-image-forget-comparison) identifies their higher
   images with abelian higher images, so def-kun-cd gives a uniform bound. Express sums
   as filtered colimits of finite partial sums, including the empty partial sum.
   Forgetting preserves these colimits (lem-weil-pbc-module-sheaves-colimits-forgetful).
   Apply lemma-weil-pbc-direct-image-filtered-colimit and finite-sum additivity
   (def-sp-left-exact-additive). Exact faithful forgetting reflects the resulting
   canonical higher-image coproduct isomorphisms, also in degree zero.
2. The module-sheaf categories are Grothendieck abelian
   (lem-weil-pbc-module-sheaves-grothendieck-abelian). Choose degreewise injective
   K-injective representatives I_i (lem-pur-kinjective-degreewise-existence).
   Their termwise sum L represents the derived coproduct, with its coprojections
   (lem-kun-grothendieck-derived-coproducts). There is no common lower bound.
3. The degree-zero injective resolution of an injective term makes every positive
   higher direct image zero. Step 1 therefore makes each term of L acyclic.
   Direct image is additive and left exact (def-weil-pbc-direct-image).
   Apply lem-kun-finite-cd-acyclic-complex with the uniform bound to I_i and L.
   Its natural comparison computes derived images and identifies their coprojections.
4. Step 1 in degree zero gives an isomorphism from the termwise sum of f_*I_i to f_*L.
   It commutes with differentials because its restriction to each summand is f_* of
   the coprojection. Localize; lem-kun-grothendieck-derived-coproducts identifies the
   source as the derived coproduct. Naturality from Step 3 identifies the result
   with the canonical comparison, proving (1).
5. For (2), use sections at the terminal object (def-weil-pbc-global-sections-functor),
   which is additive and left exact since kernels are sectionwise.
   The coefficient comparison (lem-weil-pbc-etale-module-cohomology-forget) and
   def-kun-cd give a uniform bound. On a qcqs scheme, apply
   lem-weil-pbc-cohomology-filtered-colimit to finite partial sums and use additivity
   on their injective resolutions. This gives the canonical coproduct isomorphisms
   for every higher derived sections functor, including degree zero.
6. Choose representatives I_i and their termwise sum L as in Step 2. Step 5 makes
   the terms of L acyclic for sections. Apply lem-kun-finite-cd-acyclic-complex to
   sections on I_i and L. The degree-zero comparisons commute with differentials
   by checking on each coprojection. They give an isomorphism of section complexes.
   By lem-pc-derived-module-direct-sums its localization is precisely the canonical
   comparison in D(A), proving (2). For the empty family all the complexes and their
   images are zero, so the same construction applies. -/
theorem derivedDirectImage_and_globalSections_preserveCoproducts
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
      f.torsionEtaleCohomologicalDimension < ⊤ →
        ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
          (rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) f)) ∧
      (∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
        X.torsionEtaleCohomologicalDimension < ⊤ →
          ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
            (rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) X)) := by
  sorry

end AlgebraicGeometry.Etale
