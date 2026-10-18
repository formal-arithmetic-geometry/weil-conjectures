/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.CategoryTheory.PerfectConstantLocalChainRepresentative

/-!
# Derived maps out of a perfect constant complex are locally algebraic

Source: Stacks Project, Cohomology on Sites, Tag 09BE, `lemma-locally-constant-map`
(blueprint: lem-sfb-perfect-constant-derived-map-local).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wR wS wU

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A derived morphism between constant complexes, with perfect source and arbitrary
target, is induced locally by a morphism in the coefficient ring's derived category.
Source: Stacks Project, Cohomology on Sites, Tag 09BE, `lemma-locally-constant-map`
(blueprint: lem-sfb-perfect-constant-derived-map-local).

Proof, following the node's four steps:
1. Choose a bounded finite-projective model F of P and any complex model G of L
   (def-pc-perfect-ring-complex, def-weil-abstract-derived-category). Constant
   presheaves preserve exact sequences sectionwise and module sheafification is exact
   (lem-weil-pbc-site-module-presheaf-sheafification-exact). The module action is the
   unique sheafified action (lem-pc-sites-module-sheafification-interface).
   Exact-functor derived factorization gives the natural identifications of their
   constant realizations (lem-weil-pbc-exact-functor-derived-factorization).
2. Apply lem-sfb-perfect-constant-local-chain-representative, Tag 09BD, to obtain
   actual chain representatives from the constant F to the constant G on a covering.
   The target G need not be bounded.
3. There are finitely many nonzero terms of F. On each slice identify restrictions
   of constant modules with constant modules on that slice
   (lem-weil-pbc-site-constant-restriction). Apply
   lem-weil-pbc-site-constant-morphism-local, Tag 093S(3), to each component and
   refine the covers finitely many times (def-weil-pbc-sites-and-cohomology).
   On objects not covered by the empty sieve the components are algebraic maps;
   on empty-covered objects use zero maps, since all restricted sheaves vanish.
4. On an object not covered by the empty sieve, the constant-section unit is
   injective: equality after sheafification is witnessed on a covering, which must
   have a member, and all restrictions of the constant presheaf are identities
   (lem-pc-sites-module-sheafification-interface,
   lem-pc-sites-sheafification-underlying-sets,
   lem-weil-pbc-site-sheafification-sections-local). Apply injectivity to each value
   of each chain equation. This includes the boundary degrees of F. On empty-covered
   objects the zero maps satisfy the equations. Localize each resulting algebraic
   chain map and transport through the chosen model isomorphisms. Naturality of
   exact-functor factorization identifies its constant realization with the given
   morphism on that slice. Compose the two coverings. No points are used. -/
theorem exists_perfect_constant_derived_map_local
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (X : C) (_hX : IsTerminal X)
    (R : Type (max u v)) [CommRing R]
    [HasDerivedCategory.{wR, max u v, (max u v) + 1} (ModuleCat.{max u v} R)]
    [siteModuleHasDerivedCategory.{u, v, wS}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))]
    [∀ U : C, siteModuleHasDerivedCategory.{max u v, v, wU}
      (((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)).over U)]
    (P L : DerivedCategory.{wR, max u v, (max u v) + 1} (ModuleCat.{max u v} R))
    (_hP : DerivedCategory.IsPerfectRingComplex.{max u v, wR} P)
    (φ : (siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj P ⟶
      (siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj L) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, ∃ α : P ⟶ L,
        (ringedDerivedRestrictionSized.{u, v, wS, wU}
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
          (U i)).map φ =
        (ringedDerivedRestrictionSized.{u, v, wS, wU}
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
          (U i)).map
          ((siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).map α) := by
  sorry

end CategoryTheory
