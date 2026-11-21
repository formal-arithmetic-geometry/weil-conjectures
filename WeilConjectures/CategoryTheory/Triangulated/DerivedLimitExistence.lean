/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTower

/-!
# Existence and computation of derived limits

Source: Stacks Project, Derived Categories, Tags 08TC, 07KC, 0BK6, 0BK7 and 070M.

## Main statements

- `exists_isDerivedLimit_and_iso`: existence and noncanonical uniqueness.
- `derivedCategory_countableProducts_and_towerLimit`: termwise products, their cohomology,
  and the inverse-limit computation for a K-injective representative of a tower.
-/

@[expose] public section

universe t w v u

open CategoryTheory.Limits

namespace CategoryTheory

/-- A tower with an existing product has a derived limit, unique up to isomorphism.
Source: Stacks Project, Definition 13.34.1 (Tag 08TC) and the following paragraph. -/
theorem exists_isDerivedLimit_and_iso {D : Type u} [Category.{v} D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (K : ℕ → D) [HasProduct K] (f : ∀ n : ℕ, K (n + 1) ⟶ K n) :
    (∃ L : D, IsDerivedLimit f L) ∧
      ∀ (L L' : D), IsDerivedLimit f L → IsDerivedLimit f L' → Nonempty (L ≅ L') := by
  classical
  open Pretriangulated in
    constructor
    · obtain ⟨L, p, δ, h⟩ := distinguished_cocone_triangle₁
        (towerTransitionEndomorphism f)
      exact ⟨L, p, δ, h⟩
    · intro L L' ⟨p, δ, h⟩ ⟨p', δ', h'⟩
      let T := Triangle.mk p (towerTransitionEndomorphism f) δ
      let T' := Triangle.mk p' (towerTransitionEndomorphism f) δ'
      obtain ⟨e, _⟩ := exists_iso_of_arrow_iso T.rotate T'.rotate
        (rot_of_distTriang T h) (rot_of_distTriang T' h') (Iso.refl _)
      exact ⟨(shiftFunctor D (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)⟩

/-- Exact countable products pass to the derived category and commute with cohomology;
a K-injective complex of towers computes the derived limit by its termwise inverse limit.
Source: Stacks Project, Lemma 13.34.2 (Tag 07KC), Tags 0BK6, 0BK7 and 070M.
`IsLimit` and `PreservesLimitsOfShape` record products with their projections, not merely
isomorphisms of objects. The conclusion supplies a limit cone and its derived-limit property,
without assuming an inverse limit in advance; `e` is the compatible identification of the
represented tower. -/
theorem derivedCategory_countableProducts_and_towerLimit
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A] :
    ∃ hP : HasCountableProducts (DerivedCategory A),
      letI : HasCountableProducts (DerivedCategory A) := hP
      (∀ (J : Type t) [Countable J] (C : J → CochainComplex A ℤ),
        Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor C))))) ∧
      (∀ (J : Type t) [Countable J] (p : ℤ),
        PreservesLimitsOfShape (Discrete J) (DerivedCategory.homologyFunctor A p)) ∧
      (∀ (_ : EnoughInjectives A)
        (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
        (K : ℕ → DerivedCategory A) (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
        (_e : I.asFunctor ⋙ DerivedCategory.Q ≅ Functor.ofOpSequence f),
        ∃ c : Cone I.asFunctor, Nonempty (IsLimit c) ∧
          IsDerivedLimit f (DerivedCategory.Q.obj c.pt)) := by
  obtain ⟨hP, hproducts, hhomology⟩ := derivedCategory_countableProducts_core A
  let _ := hP
  refine ⟨hP, hproducts, hhomology, ?_⟩
  exact derivedCategory_towerLimit_core A hP

end CategoryTheory
