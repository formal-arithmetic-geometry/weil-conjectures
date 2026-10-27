/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.SitePerfectModelRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-! # Local chain representatives from a strictly perfect complex

Source: Stacks Project, sites-cohomology.tex, Tag 08FR, lemma-local-actual (1),
and definition-strictly-perfect.
(blueprint: lem-sfb-ringed-site-strict-perfect-local-actual).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.StrictPerfectLocalActual

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}

/-- Forget commutativity of the coefficient sheaf, retaining its sections and restrictions.
Source: Stacks Project, Tag 08FR, the coefficient sheaf on the localized ringed site.
(blueprint: lem-sfb-ringed-site-strict-perfect-local-actual). -/
abbrev rings (R : Sheaf J CommRingCat.{max c v r}) : Sheaf J RingCat.{max c v r} :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

variable (R : Sheaf J CommRingCat.{max c v r})
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ V : C, HasDerivedCategory.{w}
    (ringedSiteModules.{max c v r} ((rings.{c, v, r} R).over V))]

/-- Restrict a derived morphism between localized complexes. The canonical localization
comparisons identify the images of termwise restriction with derived restriction.
Exactness is supplied by `overMap_exact_ofUniverses`; no arbitrary map is chosen.
Source: Stacks Project, Tag 08FR (1), with restriction as in Tag 04IX.
(blueprint: lem-sfb-ringed-site-strict-perfect-local-actual). -/
def restrict {U V : C} (f : V ⟶ U)
    {P F : CochainComplex (ringedSiteModules.{max c v r} ((rings.{c, v, r} R).over U)) ℤ}
    (u : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj F) :
    DerivedCategory.Q.obj
        (((SheafOfModules.overMap.{max c v r} (rings.{c, v, r} R) f).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj
        (((SheafOfModules.overMap.{max c v r} (rings.{c, v, r} R) f).mapHomologicalComplex
          (.up ℤ)).obj F) :=
  letI := (SheafOfModules.overMap_exact_ofUniverses.{c, v, max c v r} (rings.{c, v, r} R) f).1
  letI := (SheafOfModules.overMap_exact_ofUniverses.{c, v, max c v r} (rings.{c, v, r} R) f).2
  ((SheafOfModules.overMap.{max c v r} (rings.{c, v, r} R) f).mapDerivedCategoryFactors.app P).inv ≫
    (SheafOfModules.overMap.{max c v r} (rings.{c, v, r} R) f).mapDerivedCategory.map u ≫
      ((SheafOfModules.overMap.{max c v r} (rings.{c, v, r} R) f).mapDerivedCategoryFactors.app
        F).hom

/-- A derived morphism from a strictly perfect complex is locally an actual chain map.
The target complex is unbounded, and the covering sieve may be empty when it covers.

Source: Stacks Project, Tag 08FR, lemma-local-actual, assertion (1).
(blueprint: lem-sfb-ringed-site-strict-perfect-local-actual).

Proof: (1) Use `DerivedCategory.left_fac`, the calculus of fractions recorded by
lem-pc-quasi-isomorphisms-multiplicative-system, to write u as Q(beta) followed by
Q(f) inverse, for beta : P -> G and a quasi-isomorphism f : F -> G.
(2) Choose a below the finite support of P. Apply
lem-sfb-ringed-site-strict-perfect-local-lift with E=P, target G, source F,
u=beta and v=f. The cohomology hypotheses hold because f is a quasi-isomorphism.
This gives a covering and chain maps t such that t followed by f restricted is homotopic
to beta restricted, without any boundedness hypothesis on F or G.
(3) Restriction is exact by lem-pur-site-restriction-module-adjunction-exact,
with relocalization as in def-pur-localized-ringed-site. The natural comparison of
lem-weil-pbc-exact-functor-derived-factorization identifies the restricted fraction.
Localization factors through the homotopy category, so the homotopy gives the equality
of the two localized composites. Cancel the invertible localized denominator.
The resulting equality is exactly Q(t) = restrict R f u below. -/
theorem exists_local_chain_map (U : C)
    (P F : CochainComplex (ringedSiteModules.{max c v r} ((rings.{c, v, r} R).over U)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (hterms : ∀ j : ℤ, ∃ n : ℕ,
      Nonempty (Retract (P.X j)
        (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit ((rings.{c, v, r} R).over U))))
    (u : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj F) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ t : ((SheafOfModules.overMap.{max c v r} (rings.{c, v, r} R) f).mapHomologicalComplex
          (.up ℤ)).obj P ⟶
        ((SheafOfModules.overMap.{max c v r} (rings.{c, v, r} R) f).mapHomologicalComplex
          (.up ℤ)).obj F,
        DerivedCategory.Q.map t = restrict.{c, v, r, w} R f u := by
  sorry

end CategoryTheory.StrictPerfectLocalActual
