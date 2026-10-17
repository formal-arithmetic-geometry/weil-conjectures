module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry
open Scheme
namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- A uniform upper-amplitude bound for the derived lower shriek gives bounded-below
preservation for its right adjoint, for arbitrary Grothendieck-abelian coefficients. -/
theorem hasBoundedBelowUpperShriekWithAmplitude
    [(R(f)_![A]).IsLeftAdjoint] (N : ℤ)
    (hN : ∀ (L : DerivedCategory (Sheaf X.smallEtaleTopology A)) (n : ℤ),
      DerivedCategory.TStructure.t.IsLE L n →
        DerivedCategory.TStructure.t.IsLE ((R(f)_![A]).obj L) (n + N)) :
    HasBoundedBelowUpperShriek A f := by
  refine { plus_rightDerivedUpperShriek_obj := ?_ }
  intro K hK
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - N, ?_⟩
  change DerivedCategory.TStructure.t.IsGE ((R(f)^![A]).obj K) (n - N)
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - N - 1) (n - N) (by omega)]
  intro L φ hL
  have hL' : DerivedCategory.TStructure.t.IsLE
      ((R(f)_![A]).obj L) (n - 1) := by
    convert hN L (n - N - 1) hL using 1
    omega
  let adj := rightDerivedUpperShriekAdjunction A f
  apply (adj.homEquiv L K).symm.injective
  rw [adj.homAddEquiv_symm_zero]
  exact DerivedCategory.TStructure.t.zero _ (n - 1) n (by omega)

end Etale
end AlgebraicGeometry
