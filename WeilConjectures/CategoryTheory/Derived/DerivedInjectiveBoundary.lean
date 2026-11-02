/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Normalized connecting maps for a sequence exact on injectives

Source: Stacks Project, Tags 0117, 05TI, 05TH and 070I; Milne,
Lectures on Etale Cohomology, Section 9, Theorem 9.4.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe v u w a
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A : Type a} [Category.{w} A] [Abelian A]
  [HasDerivedCategory C] [HasDerivedCategory A] [EnoughInjectives C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
variable (S F G : C ⥤ A) [S.Additive] [F.Additive] [G.Additive]
  (ι : S ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)

omit [HasDerivedCategory C] [HasDerivedCategory A] [EnoughInjectives C] in
omit [HasDerivedCategory C] [HasDerivedCategory A] [EnoughInjectives C] in

/-- The row of section complexes associated to a natural three-term sequence.
Source: Stacks, Tag 0117. -/
def injectiveBoundaryRow (I : CochainComplex.Plus C) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex ι (.up ℤ)).app I.obj)
    ((NatTrans.mapHomologicalComplex π (.up ℤ)).app I.obj) (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, w]
      ext n
      simp)

/-- Termwise exactness on injectives gives a short exact row of complexes.
Source: Stacks, Tag 0117, degreewise criterion. -/
theorem injectiveBoundaryRow_shortExact
    (h : ∀ (I : C) [Injective I], (ShortComplex.mk (ι.app I) (π.app I)
      (NatTrans.congr_app w I)).ShortExact)
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)] :
    (injectiveBoundaryRow S F G ι π w I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact h (I.obj.X n)

/-- Exactness transports through a specified commuting triple of isomorphisms.
Source: Stacks, Tag 0117. -/
theorem exact_transport {R : ShortComplex A} (hR : R.Exact)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e₁ : R.X₁ ≅ X) (e₂ : R.X₂ ≅ Y) (e₃ : R.X₃ ≅ Z)
    (h₁ : e₁.hom ≫ f = R.f ≫ e₂.hom)
    (h₂ : e₂.hom ≫ g = R.g ≫ e₃.hom) :
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).Exact := by
  have w : f ≫ g = 0 := by
    apply (cancel_epi e₁.hom).1
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc, R.zero]
    simp
  exact ⟨w, ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂) hR⟩

omit [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
end CategoryTheory.Functor
