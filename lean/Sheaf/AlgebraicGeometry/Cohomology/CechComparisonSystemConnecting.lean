module

public import Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystem

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- The augmented injective Čech construction satisfies the connecting law.
Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: lem-pc-cech-comparison-system-existence-connecting)
Proof: For a sectionwise-surjective short exact sequence, the coefficient Čech complexes are
short exact. Horseshoe resolutions and naturality of homology boundaries give the
connecting identity for the comparison morphisms. -/
theorem cechComparisonSystem_comparison_connecting
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (comparison : ∀ q, TopCat.Sheaf.cechCohomologyFunctor U q ⟶
      Sheaf.functorH (Opens.grothendieckTopology X) q)
    (q : ℕ) (T : ShortComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))) :
    TopCat.Sheaf.cechδ U hT hg q ≫ (comparison (q + 1)).app T.X₁ =
      (comparison q).app T.X₃ ≫ Sheaf.functorHδ hT q := by
  sorry
end AlgebraicGeometry.Scheme.Modules
