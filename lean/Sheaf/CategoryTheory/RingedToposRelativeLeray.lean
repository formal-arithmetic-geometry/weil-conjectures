/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckComposablePair
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex

/-! # Relative Leray for module sheaves on ringed topoi

Source: Stacks Project, Cohomology on Sites, Tag 0734 (module assertion), via
Tags 072Z, 0731 and 015N (blueprint: lem-sfb-ringed-topos-relative-leray).

The spectral sequence and its filtration live in the functor category, recording
naturality in the source module. The composite module direct image is written
`a.modules ⋙ b.modules`: its scalar action is the composite structural ring action,
so this is the module direct image of the composite ringed-topos morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace CategoryTheory

/-- The natural relative Leray spectral sequence and its finite abutment filtration,
without flatness assumptions on either structural ring morphism.

Source: Stacks Project, Cohomology on Sites, Tag 0734
(blueprint: lem-sfb-ringed-topos-relative-leray).

Proof:
1. By lem-weil-pbc-ring-sheaves-grothendieck the three module categories are
   Grothendieck abelian. Lemma lem-sp-grothendieck-enough-injectives supplies
   injective resolutions in these categories (def-sp-injective-resolutions).
2. Put F = a.modules and G = b.modules. Their underlying direct images are
   right adjoints on sheaves of sets, hence preserve finite limits. Module
   kernels and finite products are created on underlying sheaves, so F and G
   are left exact; their induced module actions make them additive
   (def-sp-left-exact-additive). The composite structural action is
   O_E -> b_* O_D -> b_* a_* O_C, so F followed by G is (b composed with a)_*.
3. For an injective I, lem-sfb-injective-pushforward-totally-acyclic makes
   a_* I totally acyclic. Apply lem-sfb-totally-acyclic-direct-image to b:
   R^p b_*(a_* I) vanishes for p > 0. This verifies
   def-sp-composite-acyclicity without asserting that a_* preserves injectives.
4. Apply thm-sp-grothendieck to F and G. Its natural second page is
   R^p b_* R^q a_* and its abutment is R^(p+q)(F followed by G), computed by
   applying this composite to a source injective resolution, as required.
5. Its double-complex realization and thm-sp-double-complex-spectral-sequences
   give the finite decreasing filtration, top at 0 and bottom at m+1.
   The graded piece at p is the stable term E_infinity^(p,m-p).
   First-quadrant differentials vanish at (p,q) once r > max(p,q+1), giving
   the displayed stabilization. All constructions and identifications are
   natural in M, hence are objects and isomorphisms in the functor category.
-/
theorem exists_ringedTopos_relative_leray_spectralSequence
    {C D T : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory T]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology T}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (R : Sheaf L CommRingCat.{u})
    (a : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (b : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ (E : E₂CohomologicalSpectralSequenceNat
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
          ringedSiteModules.{u} ((sheafCompose L (forget₂ CommRingCat RingCat)).obj R)))
      (e₂ : ∀ p q : ℕ, (E.page 2).X (p, q) ≅
        a.modules.rightDerived q ⋙ b.modules.rightDerived p)
      (F : ∀ m : ℕ, DecreasingFiltration ((a.modules ⋙ b.modules).rightDerived m)),
      (∀ m : ℕ, (F m).step 0 = ⊤ ∧
        IsZero (Subobject.underlying.obj ((F m).step (m + 1)))) ∧
      (∀ (p q : ℕ) (r : ℤ) (hr : 2 ≤ r), max (p : ℤ) ((q : ℤ) + 1) < r →
        Nonempty ((E.page r hr).X (p, q) ≅ E.pageInfinity (p, q))) ∧
      (∀ (m p q : ℕ), p + q = m →
        Nonempty ((F m).gradedPiece (p : ℤ) ≅ E.pageInfinity (p, q))) := by
  sorry

end CategoryTheory
