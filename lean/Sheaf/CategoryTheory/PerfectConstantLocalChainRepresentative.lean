/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.CategoryTheory.SiteCoveringsCommonRefinement
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral

/-!
# Local chain representatives from a perfect constant complex

Source: Stacks Project, Cohomology on Sites, Tag 09BD,
`lemma-map-out-of-locally-constant`, via Tag 08FR(1), `lemma-local-actual`
(blueprint: lem-sfb-perfect-constant-local-chain-representative).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wS wU

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Apply the recorded constant-module functor termwise, with its canonical
zero-map instance supplied by its recorded exactness theorem. This is the ordinary
termwise constant complex, with no replacement complex chosen.
Source: Stacks Project, Cohomology on Sites, Tag 09BD
(blueprint: lem-sfb-perfect-constant-local-chain-representative). -/
def constantModuleCochainFunctor {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type (max u v)) [CommRing R] :
    CochainComplex (ModuleCat.{max u v} R) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v}
        ((constantSheaf J RingCat.{max u v}).obj (RingCat.of R))) ℤ :=
  haveI := (siteConstantModuleFunctorGeneral_exact J R).1
  (siteConstantModuleFunctorGeneral J R).mapHomologicalComplex (.up ℤ)

/-- Restrict complexes by the existing module-sheaf restriction functor. The
recorded exactness theorem supplies its canonical zero-map compatibility.
Source: Stacks Project, Modules on Sites, Section 03DH; Cohomology on Sites, Tag 09BD
(blueprint: lem-sfb-perfect-constant-local-chain-representative). -/
def moduleCochainRestriction {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (S : Sheaf J RingCat.{max u v}) (U : C) :
    CochainComplex (SheafOfModules.{max u v} S) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v} (S.over U)) ℤ :=
  haveI := (ringedOverFunctor_exactGeneral S U).1
  (SheafOfModules.overFunctor.{max u v} S U).mapHomologicalComplex (.up ℤ)

/-- The canonical localization comparison identifies restriction of a localized
complex with localization of its restriction. This uses Mathlib's factorization
isomorphism for the exact restriction functor, with no arbitrary isomorphism choice.
Source: Stacks Project, Cohomology on Sites, Tags 08JB and 09BD
(blueprint: lem-sfb-perfect-constant-local-chain-representative). -/
def moduleCochainRestrictionQIso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (S : Sheaf J RingCat.{max u v}) (U : C)
    [HasDerivedCategory.{wS} (SheafOfModules.{max u v} S)]
    [HasDerivedCategory.{wU} (SheafOfModules.{max u v} (S.over U))]
    (K : CochainComplex (SheafOfModules.{max u v} S) ℤ) :
    (ringedDerivedRestrictionSized S U).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((moduleCochainRestriction S U).obj K) :=
  haveI := (ringedOverFunctor_exactGeneral S U).1
  haveI := (ringedOverFunctor_exactGeneral S U).2.1
  haveI := (ringedOverFunctor_exactGeneral S U).2.2
  (SheafOfModules.overFunctor.{max u v} S U).mapDerivedCategoryFactors.app K

/-- Every derived map from a bounded termwise finite-projective constant complex
has chain representatives on a covering. The target complex is arbitrary.
Source: Stacks Project, Cohomology on Sites, Tag 09BD, via Tags 08FR(1), 08FQ,
08FP and 08FN (blueprint: lem-sfb-perfect-constant-local-chain-representative).

Proof, following the node's six steps:
1. Choose a finite generator surjection onto each term of F and split it by
   projectivity (def-weil-finitely-generated-module, def-weil-pbc-projective-module).
   Apply def-sf-site-constant-module-functor. Exact sheafification preserves finite
   products and zero (lem-weil-pbc-site-module-presheaf-sheafification-exact), so
   each constant term is a retract of a finite free module sheaf. The resulting
   bounded complex E is strictly perfect (Stacks 08FL).
2. By lem-pc-quasi-isomorphisms-multiplicative-system and
   lem-pc-right-fraction-representation write psi = Q(f) Q(s)^{-1}, where
   s : B -> E is a quasi-isomorphism and f : B -> G is a chain map. Its cone C is
   acyclic (lem-pur-quasi-iso-cone-acyclic). Use C^n = E^n + B^{n+1},
   d_C(x,y) = (d_E x + s y, -d_B y), and the inclusion i(x) = (x,0).
3. Restriction to slices is exact: kernels are sectionwise and epis have local
   lifts (lem-weil-pbc-module-sheaves-colimits-forgetful,
   lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective). Slice sheafification
   exists by lem-weil-pbc-site-module-presheaf-sheafification-exact. Thus C remains
   acyclic and s remains a quasi-isomorphism. The canonical comparison from
   lem-weil-pbc-exact-functor-derived-factorization defines restriction of psi.
   Retract maps remain retract maps (def-pur-localized-ringed-site).
4. A map from a finite free module to the target of an epi lifts locally: lift
   its finitely many standard basis sections and take a common refinement
   (lem-weil-pbc-module-sheaves-colimits-forgetful,
   lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective,
   lem-weil-pbc-site-coverings-common-refinement). The lifted basis defines the
   linear sheaf map by finite sums; semilinear restrictions make it natural.
   Compose with the retract inclusion to lift maps from E^q. Rank zero uses zero.
5. Starting above the upper bound of F, construct h^n : E^n -> C^{n-1} by finite
   descending induction. If the higher homotopy equations hold, then
   r^n = i^n - h^{n+1} d_E^n is a cycle: d_C r^n = 0. Acyclicity gives an epi
   C^{n-1} -> Z^n(C). Step 4 lifts r^n locally to h^n. Refine the cover at each
   step, through the lower bound of F. Transitivity makes the finite composite
   a covering (def-weil-pbc-sites-and-cohomology). Outside the interval all
   equations have zero source. Hence i = d_C h + h d_E locally. Neither B nor G
   needs a bound (def-pc-acyclic-complex-modules, def-pc-cochain-complex-modules).
6. Write h^n = (u^n,t^n). The component equations are
   id = d_E u + s t + u d_E and d_B t = t d_E. Thus t is a chain map and s t
   is homotopic to id, so Q(t) = Q(s)^{-1}. Set a = f t, obtaining
   Q(a) = Q(f) Q(s)^{-1} = psi after restriction
   (def-weil-abstract-derived-category). For the zero source the identity cover
   and zero maps suffice. -/
theorem exists_perfect_constant_local_chain_representative
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (X : C) (_hX : IsTerminal X)
    (R : Type (max u v)) [CommRing R]
    [siteModuleHasDerivedCategory.{u, v, wS}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))]
    [∀ U : C, siteModuleHasDerivedCategory.{max u v, v, wU}
      (((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)).over U)]
    (F : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q))
    [∀ q : ℤ, Module.Finite R (F.X q)]
    [∀ q : ℤ, Module.Projective R (F.X q)]
    (G : CochainComplex (SheafOfModules.{max u v}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))) ℤ)
    (ψ : DerivedCategory.Q.obj ((constantModuleCochainFunctor J.toGrothendieck R).obj F) ⟶
      DerivedCategory.Q.obj G) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, ∃ a :
        (moduleCochainRestriction
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) (U i)).obj
          ((constantModuleCochainFunctor J.toGrothendieck R).obj F) ⟶
        (moduleCochainRestriction
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) (U i)).obj G,
        DerivedCategory.Q.map a =
          (moduleCochainRestrictionQIso
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) (U i)
            ((constantModuleCochainFunctor J.toGrothendieck R).obj F)).inv ≫
          (ringedDerivedRestrictionSized
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
            (U i)).map ψ ≫
          (moduleCochainRestrictionQIso
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
            (U i) G).hom := by
  sorry

end CategoryTheory
