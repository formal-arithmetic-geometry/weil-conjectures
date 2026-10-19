/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Bounded flat subextensions

Source: blueprint `prop-coef-integral-exceptional-adjoint`, proof paragraph 2,
"derived coefficient adjunction" (blueprint: lem-coef-small-flat-subextension).
The statement is the agent-formulated finite-row input; its proof follows the bounded
local-lifting and finite-equation construction over a small ringed site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

/-- A short exact row with flat kernel admits a uniformly bounded subextension over
any prescribed bounded flat subsheaf of its quotient, with flat kernel and kernel quotient.

Source: the agent-formulated finite-row input below blueprint
`prop-coef-integral-exceptional-adjoint`, paragraph 2, "derived coefficient adjunction";
Stacks Project, Modules on Sites, Tags 03CV, 03DA, 03CY, 08FC, and Sites, Tags 00VH,
00WB, 00WK (blueprint: lem-coef-small-flat-subextension).

Proof:
1. Choose an infinite cardinal mu bounding the objects, arrows and all ring sections.
   Fix an infinite kappa at least mu with kappa^mu = kappa. Then 2^mu <= kappa,
   mu*kappa = kappa, and finite tuples and countable unions preserve the bound kappa.
   A covering restriction code records its target, its distinct arrows and one value
   per distinct arrow. Repeated arrows give equal restrictions; the original covering
   is retained for use of the site axioms (00VH).
2. For at most kappa sections S of a sheaf E, form the presheaf H_S whose sections over
   V are the R(V)-span of all restrictions of members of S. Semilinearity gives
   restriction stability, and counting restricted generators and finite linear
   combinations gives at most kappa total sections (03CV).
3. For a subpresheaf H of E, let L_E(H) consist of sections locally in H. Pullback and
   composition of coverings give restriction stability, closure under module operations,
   and gluing, so this is the smallest subsheaf containing H. Choose one restriction
   code per section. Separatedness makes equal codes determine equal sections, including
   empty coverings. Thus its size is at most mu*2^mu*kappa^mu <= kappa. Write G_E(S)
   for L_E(H_S). Its sections are locally finite linear combinations of restricted S.
4. An epimorphism of module sheaves has zero cokernel, the sheafification of its
   sectionwise cokernel (03DA). Use `lem-pc-sites-module-sheafification-interface`
   (03CY) and `lem-pc-sites-sheafification-underlying-sets` to identify its underlying
   set sheaf. The local-equality clause of
   `lem-weil-pbc-site-sheafification-sections-local` (00WB, 00WK) says every cokernel
   class becomes zero on a covering. Choose preimages there. This proves local lifting
   for epimorphisms without assuming sectionwise surjectivity.
5. Let E be the inverse-image subsheaf of C0 in B. Apply Step 4 to every section of C0,
   choosing local lifts in E, one per distinct covering arrow. There are at most
   mu*|C0| <= kappa lifts. Let N_0 = G_E(S) for their family S. Every C0 section
   locally lifts to N_0 and |N_0| <= kappa. Identify A with the sectionwise kernel of
   q using short exactness and `def-weil-sheaf-of-modules-category` (03DA).
6. Given N_j in E of size at most kappa, put K_j = A intersect N_j. For every finite
   matrix over R(V) and finite right-hand side in K_j(V) solvable in A(V), choose a
   solution. The object, coefficient and right-hand-side bounds give at most kappa
   chosen entries. Adjoin these entries, in A subset E, to all N_j sections and apply
   G_E to obtain N_{j+1}. This is increasing, bounded, and defined by ordinary recursion
   on j in the natural numbers. No sectionwise flatness of A(V) is used.
7. The sectionwise union D of all N_j is a subpresheaf with at most kappa sections.
   Put B0 = L_E(D) and A0 = A intersect B0. Then |B0| <= kappa. A finite tuple of
   B0 sections locally lies in a single N_j: refine finitely many witnessing covers
   and take the maximum stage index on each member. For an A0 tuple those sections
   also lie in A, hence in K_j. Local saturation is necessary since D need not be a sheaf.
8. If a finite system with right-hand side in A0 is solvable in A, apply Step 7 to
   that right-hand side. On each covering member it lies in some K_j. Restrict the
   coefficients and the given solution. Step 6 selected a solution in A intersect
   N_{j+1}, hence in A0. This proves local reflection of finite equations.
9. A relation in A0 is one in the flat sheaf A. Apply the forward direction of
   `lem-weil-pbc-site-flat-equational-criterion` (08FC) to factor it locally through
   finitely many A sections with the required coefficient identities. Step 8 replaces
   those sections by A0 solutions to the factorization equations. The identities
   restrict unchanged. Compose covers and apply the converse criterion to prove A0
   tensor-flat. Empty relations have the empty factorization.
10. The quotient Q = A/A0 is the sheafification of the sectionwise quotient (03DA).
    The two sheafification interfaces in Step 4 identify its underlying set sheaf.
    Local representatives from `lem-weil-pbc-site-sheafification-sections-local` lift
    Q sections locally to A. Local equality shows that an A section mapping to zero
    is locally in A0, hence globally in A0 by gluing. Finite tuples lift after finite
    common refinements. No sectionwise surjectivity of A to Q is asserted.
11. Lift a finite relation in Q locally to x_i in A. Its sum c lies in A0 by Step 10.
    The equation sum a_i*y_i = c has the solution x_i in A; Step 8 gives local
    solutions y_i in A0. Then g_i = x_i-y_i satisfy the relation in A. Factor it by
    flatness of A and 08FC, then pass to Q, where y_i vanishes. Compose all covers
    and apply the converse equational criterion to prove Q tensor-flat. This includes
    the empty relation.
12. Every C0 section locally lifts to N_0 subset B0 by Step 5. Morphisms out of C0
    agreeing after B0 to C0 therefore agree on local lifts and hence globally by
    separatedness, proving epimorphy. Its sectionwise kernel is A intersect B0 = A0
    because the given row is short exact and C0 to C is monic. Thus the new row is
    short exact (03DA). Steps 7, 9 and 11 give its size and flatness clauses with the
    fixed mu from Step 1. The construction covers C0 = 0, A = 0 and the empty site.
    It does not use flatness of C0, but that stated hypothesis is retained.
-/
theorem exists_small_flat_subextension {C : Type u} [SmallCategory C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    ∃ μ : Cardinal.{u}, Cardinal.aleph0 ≤ μ ∧
      ∀ κ : Cardinal.{u}, Cardinal.aleph0 ≤ κ → μ ≤ κ → κ ^ μ = κ →
        ∀ (S : ShortComplex (ringedSiteModules.{u}
          ((sheafCompose J.toGrothendieck
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R))),
          S.ShortExact → IsFlatOnSite (J := J.toGrothendieck) (R := R) S.X₁ →
          ∀ (C₀ : ringedSiteModules.{u}
            ((sheafCompose J.toGrothendieck
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
            (j : C₀ ⟶ S.X₃),
            Mono j → IsFlatOnSite (J := J.toGrothendieck) (R := R) C₀ →
            Cardinal.mk (Σ U : C, C₀.val.obj (op U)) ≤ κ →
            ∃ (B₀ : ringedSiteModules.{u}
                ((sheafCompose J.toGrothendieck
                  (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
              (b : B₀ ⟶ S.X₂) (t : B₀ ⟶ C₀)
              (A₀ : ringedSiteModules.{u}
                ((sheafCompose J.toGrothendieck
                  (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
              (a : A₀ ⟶ B₀) (aA : A₀ ⟶ S.X₁)
              (hzero : a ≫ t = 0),
              Mono b ∧ b ≫ S.g = t ≫ j ∧ Epi t ∧
              IsPullback a aA b S.f ∧
              (ShortComplex.mk a t hzero).ShortExact ∧
              IsFlatOnSite (J := J.toGrothendieck) (R := R) A₀ ∧
              Mono aA ∧
              IsFlatOnSite (J := J.toGrothendieck) (R := R)
                (cokernel aA) ∧
              Cardinal.mk (Σ U : C, B₀.val.obj (op U)) ≤ κ := by
  sorry

end SheafOfModules
