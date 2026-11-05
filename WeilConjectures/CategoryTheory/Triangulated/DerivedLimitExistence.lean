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
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Existence and computation of derived limits

Source: Stacks Project, Derived Categories, Tags 08TC, 07KC, 0BK6, 0BK7 and 070M
(blueprint: lem-weil-derived-limit-existence).

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
Source: Stacks Project, Definition 13.34.1 (Tag 08TC) and the following paragraph
(blueprint: lem-weil-derived-limit-existence).

Proof (clause 1 of the node): form `1 - s` using `def-weil-derived-limit`. TR1 and TR2
of `def-weil-triangulated-category` give its distinguished triangle, rotated backwards.
For two such triangles, rotate so the product terms come first. Mathlib
`Pretriangulated.exists_iso_of_arrow_iso` extends the identity arrow isomorphism to a
triangle isomorphism, using TR3 and `lem-sf-triangle-morphism-iso` (Tag 014A). Project to
the third objects and use the fully faithful shift to obtain an unshifted isomorphism.
TR3 supplies no unique extension, so no canonical isomorphism is asserted. -/
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

end CategoryTheory
