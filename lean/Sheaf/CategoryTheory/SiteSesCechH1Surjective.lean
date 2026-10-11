/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.CategoryTheory.SiteCechComplex

/-!
# Surjectivity of sections from vanishing Čech H¹

Source: Stacks Project, Cohomology on Sites, Lemma 03F8 (lemma-ses-cech-h1)
(blueprint: lem-weil-pbc-site-ses-cech-h1-surjective).

Covering indices and coefficient groups live in universes containing the site's object
and morphism universes. This includes all presieve-indexed coverings and permits larger
index and coefficient universes through `w` and `r`.
-/

@[expose] public section

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A short exact sequence of abelian sheaves on a site is surjective on sections over `U`
if the kernel has vanishing Čech H¹ on a cofinal system of coverings.
Source: Stacks Project, Cohomology on Sites, Lemma 03F8
(blueprint: lem-weil-pbc-site-ses-cech-h1-surjective).

Proof:
1. Short exactness gives a sectionwise injective kernel map, with image the kernel of
   the second map, using lem-weil-pbc-sheafification-exact and
   def-weil-pbc-exact-sequence.
2. Given a section of the quotient, the epimorphism has local lifts on a covering by
   lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective.
3. Refine this covering into the cofinal system and restrict its lifts; naturality
   preserves their images and the selected covering has vanishing Čech H¹.
4. On each double overlap take the second lift minus the first. Sectionwise exactness
   gives a unique kernel-valued cochain. On triple overlaps its alternating differential
   is zero, because the three differences cancel and the kernel map is injective.
5. By def-weil-pbc-site-cech-complex, vanishing H¹ makes this cocycle the differential
   of a 0-cochain. Subtract its image from the local lifts: they now agree on overlaps,
   and their images still equal the restrictions of the original quotient section.
6. The sheaf condition of the middle sheaf glues these corrected lifts. Separatedness
   of the quotient sheaf shows the glued section maps to the original section. -/
theorem surjective_sections_of_site_cech_h1_vanishing
    (C : Type u) [Category.{v} C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v r}))
    (hS : S.ShortExact) (U : C)
    (Cov : ∀ (I : Type (max u v w)) (V : I → C) (f : ∀ i, V i ⟶ U), Prop)
    (hcover : ∀ (I : Type (max u v w)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Cov I V f → Presieve.ofArrows V f ∈ J U)
    (hcofinal : ∀ (I : Type (max u v w)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Presieve.ofArrows V f ∈ J U →
      ∃ (K : Type (max u v w)) (W : K → C) (g : ∀ k, W k ⟶ U),
        Cov K W g ∧ ∀ k, ∃ (i : I) (t : W k ⟶ V i), t ≫ f i = g k)
    (hcech : ∀ (I : Type (max u v w)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Cov I V f → ∀ (T : SiteCechComplex V f),
        IsZero ((T.cohomologyFunctor 1).obj S.X₁.1)) :
    Function.Surjective (S.g.hom.app (op U)) := by
  sorry

end CategoryTheory
