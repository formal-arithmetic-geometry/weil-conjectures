/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Uniformly small flat subsheaves with flat quotient

Source: blueprint `prop-coef-integral-exceptional-adjoint`, proof paragraph 2,
"derived coefficient adjunction", and its agent-formulated bounded-subobject input;
Stacks Project, Modules on Sites, Tags 08FC, 03DA, 03CY; Sites, Tags 00VH, 00WB, 00WK
(blueprint: lem-coef-small-flat-subsheaf).

The cardinal bound is chosen before the flat module sheaf. The size of a module sheaf
is the cardinality of the dependent sum of its section sets over all site objects.
A monomorphism represents the subsheaf, and its cokernel is the sheaf quotient.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

/-- Every nonzero tensor-flat sheaf contains a nonzero tensor-flat subsheaf of uniformly
bounded total section size whose sheaf quotient is tensor-flat. The site, coefficient
sections, module sections and cardinals lie in the same fixed universe.

Source: the agent-formulated bounded-subobject input to blueprint
`prop-coef-integral-exceptional-adjoint`, proof paragraph 2, derived coefficient adjunction;
Stacks Project, Tags 08FC, 03DA, 03CY, 00VH, 00WB, 00WK
(blueprint: lem-coef-small-flat-subsheaf).

Proof:
1. Choose an infinite cardinal lambda bounding all site objects, all arrows and all ring
   sections, and put kappa = 2^lambda. Infinite cardinal arithmetic gives
   kappa^lambda = kappa and closure of kappa under finite tuples and countable unions.
   Encode a covering by its distinct arrows: repetitions give identical restrictions.
2. For at most kappa sections S of F, take at each V the R(V)-span of all restrictions
   of elements of S. This subpresheaf H_S is stable under restriction, because
   restrictions are semilinear. There are at most lambda times |S| generators, and
   finite sums with ring coefficients give at most kappa total sections.
3. For a subpresheaf H of F let L(H)(U) be the sections locally in H. Covering pullbacks
   give restriction stability; common refinements give closure under addition, and
   scalar multiplication preserves local membership. Glue inside F and compose the
   witnessing coverings to see that L(H) is the smallest subsheaf containing H.
   A section has a code consisting of its object, a subset of the arrows, and at most
   lambda sections of H. Separatedness makes this code injective after choosing one
   per section. Empty coverings give a unique section at their target. Thus L(H) has
   at most lambda times 2^lambda times kappa^lambda = kappa sections when |H| <= kappa.
   In particular B(S) = L(H_S) is a subsheaf of size at most kappa.
4. Choose a nonzero section s of the nonzero sheaf F and start with N_0 = B({s}).
   Given N_j of size at most kappa, consider every finite matrix over each R(V) and
   every right-hand side in N_j(V) for which the system is solvable in F(V). Choose
   one solution of each system. There are at most kappa systems and chosen entries.
   Generate N_{j+1} using all N_j sections and these entries by the construction B.
   This gives increasing subsheaves of size at most kappa, without sectionwise flatness.
5. Their sectionwise countable union D is a subpresheaf of size at most kappa. Set
   P = L(D). It contains s, has size at most kappa, and is a subsheaf. Any finite tuple
   in P locally belongs to one N_j: refine the finitely many witnessing covers and
   take the maximum of the finitely many indices on each member. The index may vary
   with the member. The union D itself need not be a sheaf.
6. A finite system with right-hand side in P and a solution in F therefore locally
   has its right-hand side in N_j. Its restricted solution witnesses solvability, so
   Step 4 chose a solution in N_{j+1}, hence in P. This proves local solution reflection.
7. For a relation among sections of P, apply flatness of F and
   `lem-weil-pbc-site-flat-equational-criterion` (Stacks 08FC) to factor it locally
   through finite free sections in F. Treat the resulting factorization equations
   as a finite system with right-hand side in P. Step 6 replaces its solutions by
   sections of P while preserving the coefficient identities. Compose the covers
   and apply the converse equational criterion to prove P flat. The empty relation
   has the empty factorization.
8. By `def-weil-sheaf-of-modules-category` (03DA), Q = F/P is the sheafification of
   the sectionwise quotient. `lem-pc-sites-module-sheafification-interface` (03CY)
   identifies its underlying abelian sheaf with abelian sheafification, and
   `lem-pc-sites-sheafification-underlying-sets` identifies the underlying set sheaf.
   Apply `lem-weil-pbc-site-sheafification-sections-local` (00WB, 00WK) to lift
   sections of Q locally to F. A section of F mapping to zero is locally in P and
   hence in P globally by gluing. Finite tuples lift over a common refinement;
   no sectionwise surjectivity of F to Q is needed.
9. Lift a finite relation in Q locally to sections f_i of F. Its sum c lies in P by
   Step 8. Step 6 solves the equation sum a_i y_i = c locally with y_i in P.
   Then g_i = f_i - y_i satisfy the relation in F. Factor this relation using F's
   flatness and 08FC; pass the factorization to Q, where the y_i vanish. The converse
   equational criterion proves Q flat. Compose the covers (00VH), including empty
   relations as in Step 7. The bound, nonvanishing and flatness of P come from Steps
   1, 5 and 7, respectively, completing all clauses with the same kappa.
-/
theorem exists_small_flat_subsheaf {C : Type u} [SmallCategory C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    ∃ κ : Cardinal.{u}, Cardinal.aleph0 ≤ κ ∧
      ∀ F : ringedSiteModules.{u}
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        ¬ IsZero F → IsFlatOnSite (J := J.toGrothendieck) (R := R) F →
          ∃ (P : ringedSiteModules.{u}
              ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
            (i : P ⟶ F),
            Mono i ∧ ¬ IsZero P ∧
              Cardinal.mk (Σ U : C, P.val.obj (op U)) ≤ κ ∧
              IsFlatOnSite (J := J.toGrothendieck) (R := R) P ∧
              IsFlatOnSite (J := J.toGrothendieck) (R := R) (cokernel i) := by
  sorry

end SheafOfModules
