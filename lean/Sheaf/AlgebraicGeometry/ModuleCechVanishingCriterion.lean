/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Paper.PQFCohomology
public import Sheaf.CategoryTheory.SiteCechComplex

/-!
# The Čech vanishing criterion for module sheaves

Source: Stacks Project, Cohomology of Sheaves, Tags 01EV and 01E1 (2)
(blueprint: lem-weil-pbc-module-cech-vanishing-criterion).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Vanishing of positive Čech cohomology for every covering of every open implies
vanishing of positive derived module cohomology on every open subscheme.
The products in `SiteCechComplex` on the poset of opens are uniquely the finite
intersections, and its index maps are the omitted-factor inclusions. Quantifying over
all choices therefore expresses the same hypothesis as the intersection Čech complex.

Source: Stacks Project, Cohomology of Sheaves, Tags 01EV and 01E1 (2)
(blueprint: lem-weil-pbc-module-cech-vanishing-criterion).

Proof (the nine steps of the node):
1. Induct on positive degree, simultaneously for all Čech-acyclic module sheaves.
2. Embed such a sheaf G into an injective I and take its cokernel Q, using
   lem-weil-pbc-scheme-modules-enough-injectives, def-sp-injective-resolutions and
   def-weil-pbc-exact-sequence in the abelian module category.
3. I is Čech-acyclic by lem-weil-pbc-module-injective-open-cover-cech-acyclic (01EP).
4. Kernels are sectionwise. Apply lem-weil-pbc-module-ses-cech-h1-surjective (01EU)
   to all coverings of each open W: vanishing Čech H¹(G) makes I(W) → Q(W) surjective.
   Thus the sequence is short exact as presheaves, not just as sheaves.
5. Taking products of these sectionwise short exact sequences on the intersections
   gives a short exact sequence of Čech complexes (def-weil-pbc-site-cech-complex and
   lem-weil-pbc-cochain-complexes-degreewise-exact).
6. Its long exact cohomology sequence, lem-weil-pbc-complex-ses-homology-long-exact,
   places positive Čech Hᵖ(Q) between zero groups Hᵖ(I) and Hᵖ⁺¹(G). Hence Q is
   again Čech-acyclic.
7. Restrict the short exact sequence to U. Restriction is exact and preserves injectives
   by lem-weil-pbc-module-open-restriction-injectives (01E1); its sections agree with
   the original sections on U by lem-weil-pbc-module-restriction-open-immersion-colimits.
8. By pqf-def-cohomology and def-sp-left-exact-additive, cohomology of U is derived
   global sections in modules, computed with injective resolutions.
9. Apply lem-weil-pbc-derived-functor-long-exact to the restricted sequence. Positive
   cohomology of I vanishes by lem-weil-pbc-derived-functor-injective-vanishing (015B).
   In degree one, R⁰Γ ≅ Γ (lem-weil-pbc-right-derived-universal-delta-functor) and
   surjectivity in step 4 imply H¹(G) = 0. In higher degrees the induction hypothesis
   for Q from step 6 and the exact sequence imply Hᵖ(G) = 0. Apply this to F. -/
theorem module_cohomology_isZero_of_cech_vanishing (X : Scheme.{u}) (F : X.Modules)
    (hcech : ∀ (U : X.Opens) (I : Type (max u w)) (V : I → X.Opens)
      (hom : ∀ i, V i ⟶ U), (⨆ i, V i) = U →
      ∀ (S : SiteCechComplex V hom) (p : ℕ), 0 < p →
        IsZero ((S.cohomologyFunctor p).obj ((toPresheaf X).obj F))) :
    ∀ (U : X.Opens) (p : ℕ), 0 < p →
      IsZero ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj
        ((restrictFunctor U.ι).obj F)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
