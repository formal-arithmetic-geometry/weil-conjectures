module
public import Sheaf.RingTheory.Depth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Boundary points of the smooth pullback have stalk dimension at least two.
Source: Stacks Project, Tags 0EYJ, 0337, 00LK, 033C and 00H8.
(blueprint: new-stalk-normalization-boundary-dimension-two-target)
Proof: minimality of s identifies the boundary with the closed fibre; smoothness
and the flat local depth formula give depth at least two, and depth is bounded by
the Krull dimension of the stalk. -/
theorem stalk_normalization_boundary_dimension_two_target {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    let a := S.fromSpecStalk s
    ∀ y : (pullback c a : Scheme.{u}),
      y ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤
        ringKrullDim ((pullback c a).presheaf.stalk y) := by
  sorry

end AlgebraicGeometry.Scheme
