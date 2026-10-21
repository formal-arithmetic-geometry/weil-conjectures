/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Deriving the principal quotient Roos functor

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.PrincipalQuotientCompletion

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})

variable [HasDerivedCategory.{w}
  (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]

/-- The quotient Roos functor has a universal left derived functor, computed
on every K-flat cochain complex.

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941, and
Derived Categories, Tag 06XN (blueprint: lem-pur-principal-quotient-roos-derived).

Proof: Tensor homotopies with the fixed quotient complexes. Naturality in their
transition maps assembles these homotopies on the tower. Products and the signed
cone carry them to homotopies of the Roos complexes by the existing strict Roos
compatible-homotopy theorem, giving a functor on the homotopy category. If a map
between K-flat complexes is a quasi-isomorphism,
resolve each fixed quotient by a K-flat complex and use the tensor square and
two-out-of-three to see that tensoring the map with that quotient is a
quasi-isomorphism. Exact countable products preserve these maps, and the cone
triangle makes their Roos map a quasi-isomorphism. K-flat resolutions give a
resolving class on the homotopy category. The resolving-class essential-constancy
criterion and its pointwise Kan-extension bridge give the total left derived
functor; using the identity resolution shows its counit invertible on every
K-flat object. Precompose its universal counit with the full, essentially
surjective homotopy quotient and transport along quotientCompQhIso. This gives
the asserted cochain universal pair and preserves all computation isomorphisms.
No unit augmentation is involved in this construction. -/
theorem exists_derivedQuotientRoos
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))] :
    ∃ (L : DerivedCategory.{w} (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
        DerivedCategory.{w} (ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R)))
      (ε : DerivedCategory.Q ⋙ L ⟶ quotientRoos R t ⋙ DerivedCategory.Q),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
        ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          IsIso (ε.app P) := by sorry

end CategoryTheory.PrincipalQuotientCompletion
