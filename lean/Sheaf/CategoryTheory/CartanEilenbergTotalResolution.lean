/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.KInjectiveBridge

/-! # The augmented Cartan--Eilenberg total complex

Source: blueprint thm-sp-if-e1, proof paragraph 2; Stacks Tags 0133 and 015J.
(blueprint: lem-sp-cartan-eilenberg-total-resolution).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The total of bounded-below injective rows is a K-injective resolution, with the
augmentation specified on its degree-zero summands.
Source: blueprint thm-sp-if-e1, proof paragraph 2; Stacks Tags 0133 and 015J.
(blueprint: lem-sp-cartan-eilenberg-total-resolution).

Proof.
1. Extend each nonnegative resolution by zero and flip. The maps from K into
resolution degree zero commute with the total differential: their resolution differential
is zero, and their complex differential commutes with the augmentation a. They therefore
assemble into the displayed augmentation.
2. Fix a lower bound b for I. In degree n only resolution degrees 0 through n-b
contribute. Thus the total is zero below b and its terms are finite sums of injectives.
A finite sum of injectives is injective, and a bounded-below complex of injectives is
K-injective by lem-sp-kinjective-computes.
3. After adjusting the cone signs, the cone of the augmentation is the total of
the rows augmented by K^s in resolution degree -1. Each augmented row is acyclic
by hrows. Its filtration by complex degree is finite in every cochain degree;
the associated first page vanishes. Bounded convergence makes the cone
acyclic. Hence the augmentation is a quasi-isomorphism. -/
theorem cartanEilenberg_total_resolution
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex.Plus A)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K.obj ⟶ I)
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (hterms : ∀ (s : ℤ) (r : ℕ), Injective ((I.X s).X r))
    (hrows : ∀ s : ℤ, QuasiIso (a.f s)) :
    ∃ (aug : K.obj ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
        (ComplexShape.up ℤ)),
          (∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
            (HomologicalComplex.extendXIso
              (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
              ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
            (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
              (ComplexShape.up ℤ) 0 n n (zero_add n)) ∧
      QuasiIso aug ∧
      CochainComplex.IsKInjective
        ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
          (ComplexShape.up ℤ)) := by sorry

end CategoryTheory.Functor
