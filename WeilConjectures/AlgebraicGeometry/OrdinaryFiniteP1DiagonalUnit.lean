/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalTriangles

/-!
# The diagonal unit for the Kummer-normalized projective-line trace
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] ordinaryFinitePullback ordinaryFinitePushforward
  ordinaryFiniteTensor

-- Preserve the existing binder names in the public statement.
set_option linter.unusedVariables false in
/-- The supported diagonal gives a unit for the already specified trace counit.
The decomposition and Chern arrows are inputs; no decomposition is asserted here. -/
theorem ordinaryFiniteP1_diagonal_unit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (c : OrdinaryFiniteP1ChernFamily A N hA)
    (hc : OrdinaryFiniteP1ChernFamilySpec A N hA c)
    (b : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
        (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    (hb : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      (b S hS).hom = ordinaryFiniteP1KummerMap A N hA t c S hS)
    (hbc : OrdinaryFiniteP1KummerMapBaseChange A N hA t c) :
    (∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      ∃ η : 𝟭 (DerivedCategoryModule A (ProjectiveLine S)) ⟶
          ordinaryFinitePushforward A (ProjectiveLine S ↘ S) ⋙
            ordinaryFiniteP1Right A N hA S,
        (∀ M : DerivedCategoryModule A (ProjectiveLine S),
          (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map (η.app M) ≫
            (ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app
              ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj M) = 𝟙 _) ∧
        (∀ K : DerivedCategoryModule A S,
          η.app ((ordinaryFiniteP1Right A N hA S).obj K) ≫
            (ordinaryFiniteP1Right A N hA S).map
              ((ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app K) = 𝟙 _)) ∧
    (∀ {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
      (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤)))
      (K : DerivedCategoryModule A S),
      (ordinaryFinitePullback A f).map
          ((ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app K) =
        ordinaryFiniteP1Exchange A f ((ordinaryFiniteP1Right A N hA S).obj K) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteP1RightBaseChange A N hA t f
              (affineTraceProjectiveInvertible N S hS) K).hom ≫
          (ordinaryFiniteP1TraceCounit A N hA S' (b S' hS')).app
            ((ordinaryFinitePullback A f).obj K)) := by
  exact ⟨ordinaryFiniteP1_diagonal_triangles N hN A hA t c hc b hb hbc,
    ordinaryFiniteP1_diagonal_baseChange N hN A hA t c hc b hb hbc⟩

end AlgebraicGeometry.Etale
