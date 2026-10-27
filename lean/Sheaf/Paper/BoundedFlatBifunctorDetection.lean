/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Functor.Currying
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import Sheaf.Paper.BoundedFlatReplacement
import Sheaf.AlgebraicGeometry.TruncationHomotopyColimit

/-!
# Bounded flat test pairs detect isomorphisms of bifunctors

Source: blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lem-kun-0f1n.proof.md, paragraphs 2-4; Stacks Project, Tag 0F1N.
(blueprint: lem-kun-bounded-flat-bifunctor-detection).

The bifunctors are curried. Each partial functor has its own specified shift
comparison; no compatibility between shifts in the two different variables is assumed.
Boundedness here is termwise boundedness, not boundedness only of cohomology.
-/

@[expose] public section

set_option autoImplicit false

universe u vT uT

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- Bounded complexes, flat only in the first variable, detect invertibility of a
shift-compatible transformation between separately exact, countable-coproduct-preserving
bifunctors on unbounded etale derived categories.

Source: blueprint lem-kun-0f1n.proof.md, paragraphs 2-4; Stacks Project, Tag 0F1N
(blueprint: lem-kun-bounded-flat-bifunctor-detection).

Proof:
1. Fix one input. Naturality and the coproduct universal property show that the
   component on a countable sum is invertible if all its summand components are:
   construct the inverse by its restrictions to the coprojections. Exactness gives
   additivity, hence preservation of the telescope arrow 1-s
   (def-weil-pbc-category-colimit, def-weil-triangulated-category, def-kun-truncations).
2. Exactness sends a telescope triangle to a distinguished triangle
   (lem-kun-functor-preserves-hocolim). Naturality at all three arrows and shift
   compatibility at 1 make the specified components a morphism of triangles.
   Two-out-of-three (lem-sf-triangle-morphism-iso) proves closure of invertibility
   under sequential homotopy colimits in either variable.
3. For bounded-above P with flat terms and bounded-above R, their stupid lower
   truncations are bounded, and those of P remain flat (def-pc-flat-sheaf-modules).
   The hypothesis applies to every truncated pair. The truncations of R stabilize
   degreewise to R, so their colimit is R and represents its homotopy colimit
   (def-kun-truncations, lem-kun-complex-colimit-hocolim). Step 2 gives invertibility
   at each truncated P paired with R.
4. The same stabilization and homotopy-colimit argument in P gives invertibility
   for every bounded-above flat P and bounded-above R.
5. Replace a bounded-above representative of the first input by a bounded-above
   flat complex (lem-kun-bounded-flat-replacement). Its quasi-isomorphism becomes
   invertible under localization (def-weil-abstract-derived-category). Naturality
   transports Step 4 along this isomorphism. No flatness of the second input is used.
6. Represent arbitrary inputs by complexes (def-weil-pbc-derived-categories).
   Their good upper truncations are bounded above (def-kun-truncations). Step 5
   applies to every pair. The second input is the homotopy colimit of its good
   upper truncations (lem-kun-hocolim-truncations), so Step 2 gives invertibility
   with any fixed upper truncation of the first input.
7. Apply lem-kun-hocolim-truncations and Step 2 in the first input, keeping the
   original arbitrary second input fixed. Naturality transports along the
   telescope isomorphism and gives the required component at the original inputs. -/
theorem isIso_of_bounded_flat_test_pairs
    (U V : AlgebraicGeometry.Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    {T : Type uT} [Category.{vT} T] [Preadditive T] [HasZeroObject T]
    [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
    [Pretriangulated T] [CategoryTheory.IsTriangulated T] [HasCountableCoproducts T]
    (A B : DerivedCategoryModule Λ U ⥤ DerivedCategoryModule Λ V ⥤ T)
    [∀ E, (A.obj E).CommShift ℤ] [∀ E, (B.obj E).CommShift ℤ]
    [∀ F, (A.flip.obj F).CommShift ℤ] [∀ F, (B.flip.obj F).CommShift ℤ]
    [∀ E, (A.obj E).IsTriangulated] [∀ E, (B.obj E).IsTriangulated]
    [∀ F, (A.flip.obj F).IsTriangulated] [∀ F, (B.flip.obj F).IsTriangulated]
    [∀ E, PreservesColimitsOfShape (Discrete ℕ) (A.obj E)]
    [∀ E, PreservesColimitsOfShape (Discrete ℕ) (B.obj E)]
    [∀ F, PreservesColimitsOfShape (Discrete ℕ) (A.flip.obj F)]
    [∀ F, PreservesColimitsOfShape (Discrete ℕ) (B.flip.obj F)]
    (α : A ⟶ B)
    [∀ E, NatTrans.CommShift (α.app E) ℤ]
    [∀ F, NatTrans.CommShift (α.flipApp F) ℤ]
    (hα : ∀ (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
      (R : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ),
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) →
      (∀ i : ℤ, exactFunctor _ _ (tensorRight (P.X i))) →
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (R.X i)) →
      IsIso ((α.app (_root_.DerivedCategory.Q.obj P)).app
        (_root_.DerivedCategory.Q.obj R))) :
    ∀ (E : DerivedCategoryModule Λ U) (F : DerivedCategoryModule Λ V),
      IsIso ((α.app E).app F) := by
  sorry

end AlgebraicGeometry.Etale
