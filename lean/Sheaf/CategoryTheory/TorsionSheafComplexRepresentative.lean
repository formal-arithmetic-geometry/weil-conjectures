/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Abelian

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.CategoryTheory.TorsionInjectiveSubcomplex

/-!
# Bounded-below torsion-sheaf complex representatives

Source: Stacks Project, Cohomology on Sites, Tag 0DD7, `lemma-torsion`, and
Étale Cohomology, Tag 0DE5, `lemma-cohomological-descent-etale-ph`, first proof paragraph
(blueprint: lem-trf-torsion-sheaf-complex-representative).
-/

@[expose] public section

set_option autoImplicit false

universe u v t w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- A bounded-below derived object with torsion cohomology has a bounded-below
representative whose terms are torsion sheaves. Torsion is local on the site:
the annihilating positive integer may vary with the section and the covering member.
Source: Stacks Project, Tag 0DD7, `lemma-torsion`, bounded-below consequence used in
Tag 0DE5, `lemma-cohomological-descent-etale-ph`, first proof paragraph
(blueprint: lem-trf-torsion-sheaf-complex-representative).

Proof:
1. Choose a lower cohomology bound a from hK. Abelian sheaves on a small site have
   enough injectives (lem-weil-pbc-site-sheaves-enough-injectives). Apply clause (1)
   of lem-weil-pbc-dplus-injective-representative to obtain a complex I of injective
   sheaves, zero below a, with Q(I) isomorphic to K. The factorization of cohomology
   through Q identifies H^r(I) with H^r(K), so all H^r(I) are torsion.
2. Apply lem-trf-torsion-injective-subcomplex (the claim in the proof of 0DD7).
   The torsion subsheaves of the terms of I form a subcomplex L, since the
   differentials preserve locally annihilated sections. Its inclusion into I is a
   quasi-isomorphism: injective abelian sheaves are divisible, giving a short exact
   sequence 0 -> L -> I -> I tensor Q -> 0, and flatness of Q makes the last complex
   acyclic. Every L^r is torsion and L vanishes below a. Localization inverts the
   inclusion; compose Q(L) isomorphic to Q(I) with Q(I) isomorphic to K.
   No common annihilator is chosen at any stage. -/
theorem exists_torsion_complex_representative
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    (_hJ : J.IsSiteForCoverings)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v t}]
    [HasDerivedCategory.{w} (Sheaf J.toGrothendieck AddCommGrpCat.{max u v t})]
    (K : DerivedCategory (Sheaf J.toGrothendieck AddCommGrpCat.{max u v t}))
    (hK : ∃ a : ℤ, ∀ r : ℤ, r < a →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max u v t}) r).obj K))
    (hT : ∀ r : ℤ, ((DerivedCategory.homologyFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v t}) r).obj K).IsTorsion) :
    ∃ (a : ℤ) (L : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v t}) ℤ),
      (∀ r : ℤ, r < a → IsZero (L.X r)) ∧
      (∀ r : ℤ, (L.X r).IsTorsion) ∧ Nonempty (DerivedCategory.Q.obj L ≅ K) := by
  sorry

end CategoryTheory.Sheaf
