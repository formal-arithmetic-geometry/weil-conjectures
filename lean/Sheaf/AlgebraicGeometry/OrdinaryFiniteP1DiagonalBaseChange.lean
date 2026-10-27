/-
Copyright (c) 2026 The SHEAF contributors.
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalIntegral
import Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceBaseChange
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-ordinary-finite-p1-diagonal-base-change).

# Base change of the specified projective-line trace counit

Source: blueprint thm-amb-p1-adjunction.proof.md.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
theorem ordinaryFiniteP1_diagonal_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (c : OrdinaryFiniteP1ChernFamily A N hA)
    (_hc : OrdinaryFiniteP1ChernFamilySpec A N hA c)
    (b : ∀ (S : Scheme.{u}) [IsNoetherian S] (_hS : IsUnit (N : Γ(S, ⊤))),
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
        (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    (hb : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      (b S hS).hom = ordinaryFiniteP1KummerMap A N hA t c S hS)
    (hbc : OrdinaryFiniteP1KummerMapBaseChange A N hA t c) :
    (∀ {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
      (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤)))
      (K : DerivedCategoryModule A S),
      (ordinaryFinitePullback A f).map
          ((ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app K) =
        ordinaryFiniteP1Exchange A f ((ordinaryFiniteP1Right A N hA S).obj K) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteP1RightBaseChange A N hA t f
              (ordinaryFiniteP1_isUnit N S hS) K).hom ≫
          (ordinaryFiniteP1TraceCounit A N hA S' (b S' hS')).app
            ((ordinaryFinitePullback A f).obj K))   := by
  intro S' S _ _ f hS hS' K
  apply ordinaryFiniteP1TraceCounit_baseChange N hN A hA t f hS hS'
  exact ordinaryFiniteP1_scalarTrace_baseChange N A hA t c b hb hbc f hS hS'
end AlgebraicGeometry.Etale
