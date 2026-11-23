/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckDerivedPerfectWellGeneratorsSupport
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # A small perfect family of well-generators for a Grothendieck derived category -/

@[expose] public section

universe v u u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Images of a compact generating family generate after an exact localization. -/
private theorem compact_localization_images_generate
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    [HasCoproducts.{v} C] [HasCoproducts.{v} D]
    {J : Type v} (E : J → C) (hcompact : ∀ j, IsCompactObject (E j))
    (hgen : IsTriangulatedGeneratingFamily E) (L : C ⥤ D) (R : D ⥤ C)
    (adj : L ⊣ R) [L.CommShift ℤ] [L.IsTriangulated] (hc : IsIso adj.counit)
    (T : ObjectProperty D) [T.IsClosedUnderIsomorphisms] [T.IsTriangulated]
    (hTsum : ∀ (I : Type v) (Y : I → D), (∀ i, T (Y i)) → T (∐ Y))
    (hET : ∀ j, T (L.obj (E j))) : ∀ Y, T Y := by
  have : L.IsLeftAdjoint := ⟨R, ⟨adj⟩⟩
  let P := T.inverseImage L
  have hPsum (I : Type v) (X : I → C) (hX : ∀ i, P (X i)) : P (∐ X) := by
    exact T.prop_of_iso (asIso (sigmaComparison L X)) (hTsum I _ hX)
  have hPshape (X : C)
      (hX : ∃ (I : Type v) (a : I → J) (n : I → ℤ),
        Nonempty (X ≅ ∐ fun i ↦ (E (a i))⟦n i⟧)) : P X := by
    obtain ⟨I, a, n, ⟨e⟩⟩ := hX
    exact P.prop_of_iso e.symm
      (hPsum I _ (fun i ↦ P.le_shift (n i) _ (hET (a i))))
  have hPall (X : C) : P X := by
    obtain ⟨Xn, t, hX₀, ⟨Z, a, b, hZ, htri⟩, q, r, htel⟩ :=
      compactGenerators_buildObjects.{v, v} E hcompact hgen X
    have hXn (n : ℕ) : P (Xn n) := by
      induction n with
      | zero => exact hPshape _ hX₀
      | succ n hn =>
        exact P.ext_of_isTriangulatedClosed₃ _ (htri n) (hPshape _ (hZ n)) hn
    have hsum := hPsum (ULift.{v} ℕ) (fun n ↦ Xn n.down) (fun n ↦ hXn n.down)
    exact P.ext_of_isTriangulatedClosed₃ _ htel hsum hsum
  intro Y
  let _ := hc
  exact T.prop_of_iso (asIso (adj.counit.app Y)) (hPall (R.obj Y))

/-- A Grothendieck derived category has small shift-closed perfect well-generators.

Source: Neeman, On the derived category of sheaves on a manifold, Theorem 0.2
and Section 2. -/
theorem derived_exists_perfect_well_generators
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A] :
    ∃ (G : ObjectProperty (DerivedCategory A)) (κ : Cardinal.{v})
      (_ : Fact κ.IsRegular),
      ObjectProperty.EssentiallySmall.{v} G ∧ G.IsStableUnderShift ℤ ∧
      (∀ U, G U → IsAlphaSmall U κ) ∧ G.IsCoproductFactorizationClass ∧
      ∀ (S : ObjectProperty (DerivedCategory A)) [S.IsClosedUnderIsomorphisms]
        [S.IsTriangulated],
        (∀ (I : Type v) (Y : I → DerivedCategory A), (∀ i, S (Y i)) → S (∐ Y)) →
        G ≤ S → ∀ U, S U := by
  obtain ⟨B, cB, zB, sB, pB, aB, tB, iB, sumsB, J, E, hcompact, hgen,
      L, R, adj, sL, hLtri, hc, G, κ, hκ, hGsmall, hGshift, hGsmallness,
      hGfactor, hGE⟩ :=
    exists_small_factorization_class_of_compact_localization (A := A)
  set_option linter.style.haveILetI false in
  letI := cB
  set_option linter.style.haveILetI false in
  letI := zB
  set_option linter.style.haveILetI false in
  letI := sB
  set_option linter.style.haveILetI false in
  letI := pB
  set_option linter.style.haveILetI false in
  letI := aB
  set_option linter.style.haveILetI false in
  letI := tB
  set_option linter.style.haveILetI false in
  letI := iB
  set_option linter.style.haveILetI false in
  letI := sumsB
  set_option linter.style.haveILetI false in
  letI := sL
  set_option linter.style.haveILetI false in
  letI := hLtri
  set_option linter.style.haveILetI false in
  letI := hc
  refine ⟨G, κ, hκ, hGsmall, hGshift, hGsmallness, hGfactor, ?_⟩
  intro T hTi hTt hTsum hGT
  exact compact_localization_images_generate (C := B) (D := DerivedCategory A)
    E hcompact hgen L R adj hc T hTsum (fun j ↦ hGT _ (hGE j))

end CategoryTheory
