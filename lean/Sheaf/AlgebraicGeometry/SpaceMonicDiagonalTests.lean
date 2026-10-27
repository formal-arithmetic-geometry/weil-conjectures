/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-! # Diagonal scheme tests for a monomorphism into a base change

Source: Stacks Project, Morphisms of Spaces, Tags 03KL and 03KQ,
with the sectionwise monomorphism specialization
(blueprint: lem-a1-space-monic-diagonal-tests).

The comparison and restriction maps are the canonical maps of presheaf pullbacks.
The theorem asserts invertibility, compatibility with further tests, and preservation
of closed-immersion scheme tests, using the existing representability predicate.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The pair of images in `X` of two sections of `Y` with a common `B` component.
Source: Stacks, Tags 03KL and 03KQ, diagonal pullback formula
(blueprint: lem-a1-space-monic-diagonal-tests). -/
def monicDiagonalPairMap {S : Scheme.{u}} {T B : Over S}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T) (b : B ⟶ T)
    (j : Y ⟶ Limits.pullback f (yoneda.map b)) :
    Limits.pullback (j ≫ pullback.snd f (yoneda.map b))
        (j ≫ pullback.snd f (yoneda.map b)) ⟶ Limits.pullback f f :=
  pullback.map _ _ f f (j ≫ pullback.fst f (yoneda.map b))
    (j ≫ pullback.fst f (yoneda.map b)) (yoneda.map b)
    (by simp only [Category.assoc, ← pullback.condition])
    (by simp only [Category.assoc, ← pullback.condition])

/-- The canonical comparison sends `(u,y)` to `(u,r(y))` over the test scheme.
Source: Stacks, Tags 03KL and 03KQ, diagonal pullback formula
(blueprint: lem-a1-space-monic-diagonal-tests). -/
def monicDiagonalTestMap {S : Scheme.{u}} {T B D : Over S}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T) (b : B ⟶ T)
    (j : Y ⟶ Limits.pullback f (yoneda.map b))
    (d : yoneda.obj D ⟶ Limits.pullback (j ≫ pullback.snd f (yoneda.map b))
      (j ≫ pullback.snd f (yoneda.map b))) :
    Limits.pullback d (pullback.diagonal (j ≫ pullback.snd f (yoneda.map b))) ⟶
      Limits.pullback (d ≫ monicDiagonalPairMap f b j) (pullback.diagonal f) :=
  pullback.map _ _ _ _ (𝟙 _) (j ≫ pullback.fst f (yoneda.map b))
    (monicDiagonalPairMap f b j) (by simp)
    (by ext <;> simp [monicDiagonalPairMap, pullback.diagonal])

/-- The map between diagonal tests induced by a further scheme test.
Source: Stacks, Tags 03KL and 03KQ, restriction of the diagonal pullback formula
(blueprint: lem-a1-space-monic-diagonal-tests). -/
def diagonalTestRestriction {S : Scheme.{u}} {D D' : Over S}
    {F H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ H) (d : yoneda.obj D ⟶ H)
    (v : D' ⟶ D) : Limits.pullback (yoneda.map v ≫ d) a ⟶ Limits.pullback d a :=
  pullback.map _ _ _ _ (yoneda.map v) (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The canonical diagonal-test comparison is an isomorphism over each test scheme,
and is natural in further scheme tests. Closed-immersion scheme tests of `Δ_X/T`
therefore give closed-immersion scheme tests of `Δ_Y/B`.

Source: Stacks Project, Morphisms of Spaces, Tags 03KL and 03KQ, sectionwise
monomorphism specialization (blueprint: lem-a1-space-monic-diagonal-tests).

Proof:
1. On a scheme `E`, the left test has pairs `(u,y)` with
   `y = y₁|u = y₂|u`; the right test has pairs `(u,x)` with
   `x = x₁|u = x₂|u` (def-trf-algebraic-space).
2. Both sections of `Y` have the same `B` component. Equality of their images
   in `X` thus gives equality of their images under `j`, and injectivity of
   `j` gives their equality. The converse follows by applying the first projection.
3. The displayed comparison sends `(u,y)` to `(u,r(y))`; its inverse sends
   `(u,x)` to `(u,y₁|u)`. The pair descriptions show both composites are identities.
   Both formulas commute with restriction, and with every further scheme test.
4. Represent the right test by a scheme `Z` closed-immersed in `D`. Composing
   its representation with the inverse comparison represents the left test by
   the very same `Z → D` (def-weil-closed-immersion).
   The identity on `X_B` is injective on sections, so this includes `Y = X_B`;
   fibreProduct_isAlgebraicSpace supplies its algebraic-space property
   (lem-trf-space-fibre-products-etale-covers). -/
theorem space_monic_diagonal_tests {S : Scheme.{u}} (T B : Over S) (b : B ⟶ T)
    (X Y : AlgebraicSpace S) (f : X.obj.obj ⟶ yoneda.obj T)
    (j : Y.obj.obj ⟶ Limits.pullback f (yoneda.map b))
    (hj : ∀ E : Over S, Function.Injective (j.app (op E))) :
    (∀ (D : Over S)
      (d : yoneda.obj D ⟶ Limits.pullback (j ≫ pullback.snd f (yoneda.map b))
        (j ≫ pullback.snd f (yoneda.map b))),
      IsIso (monicDiagonalTestMap f b j d) ∧
      monicDiagonalTestMap f b j d ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      ∀ (D' : Over S) (v : D' ⟶ D),
        diagonalTestRestriction (pullback.diagonal (j ≫ pullback.snd f (yoneda.map b)))
            d v ≫ monicDiagonalTestMap f b j d =
          monicDiagonalTestMap f b j (yoneda.map v ≫ d) ≫
            diagonalTestRestriction (pullback.diagonal f)
              (d ≫ monicDiagonalPairMap f b j) v) ∧
    (IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal f) →
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (pullback.diagonal (j ≫ pullback.snd f (yoneda.map b)))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
