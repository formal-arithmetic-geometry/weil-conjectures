/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Exact countable products of pro-etale module sheaves

Source: Bhatt--Scholze, The pro-etale topology for schemes, Propositions 3.1.9,
3.2.3 (1), and 4.2.8; Stacks Project, Tags 03DB and 0947 (4)
(blueprint: lem-weil-proetale-countable-products-exact).
-/

@[expose] public section

universe t u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Countable products exist, evaluation computes them sectionwise, and a product
of epimorphisms is an epimorphism. Preservation by evaluation identifies the
canonical product cone with the product of section modules; thus both scalar actions
and restriction maps are coordinatewise. Surjectivity here is sheaf surjectivity,
expressed categorically by `Epi`, not surjectivity on every object's sections.

Source: Bhatt--Scholze, Propositions 3.1.9, 3.2.3 (1), 4.2.8;
Stacks Project, Tags 03DB and 0947 (4)
(blueprint: lem-weil-proetale-countable-products-exact).

Proof for stage 3:
1. Apply lem-weil-pbc-module-sheaves-limits-sectionwise to discrete countable
   diagrams. Mathlib's module-sheaf limits give the product universal property,
   coordinatewise scalar actions, restrictions, and the evaluation identification.
2. Kernels are sectionwise by def-weil-sheaf-of-modules-category. The product
   functor is additive and preserves kernels and zero objects, hence is left exact.
3. For each site object use lem-weil-pbc-proetale-affine-wcontractible-covering-family
   to choose a cover by affine weakly contractible objects. By
   lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits, each given
   epimorphism is surjective on sections over each member of this cover.
4. Choose lifts of all coordinates over each fixed covering object, using ordinary
   set-theoretic choice. The sectionwise product formula assembles these lifts
   into a section of the product source mapping to the restricted target section.
5. If two maps out of the product target agree after composition with the product
   map, these local lifts make their values agree over the cover. Separatedness
   from def-weil-pbc-sites-and-cohomology gives equality of their values downstairs.
   They therefore agree, proving `Epi`. With step 2 this proves exactness.
The same argument works in every coefficient universe containing the site. -/
theorem countableProducts_exact (Y : Scheme.{t})
    (R : Sheaf (topology Y) CommRingCat.{max u (t + 1)}) :
    HasCountableProducts
      (ringedSiteModules.{max u (t + 1)}
        ((sheafCompose (topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)) ∧
    (∀ (I : Type w) [Countable I] (U : Y.ProEt),
      PreservesLimitsOfShape (Discrete I)
        (SheafOfModules.evaluation.{max u (t + 1)}
          ((sheafCompose (topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
          (op U))) ∧
    (∀ (I : Type w) [Countable I]
      (F G : I → ringedSiteModules.{max u (t + 1)}
        ((sheafCompose (topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
      (f : ∀ i : I, F i ⟶ G i), (∀ i : I, Epi (f i)) → Epi (Limits.Pi.map f)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
