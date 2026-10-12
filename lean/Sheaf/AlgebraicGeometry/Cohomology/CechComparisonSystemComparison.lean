module

public import Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystem

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Existence of the comparison morphisms and their degree-zero normalization.
Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: lem-pc-cech-comparison-system-existence-comparison)
Proof: The augmented injective Čech double complex supplies the comparison in every degree;
its degree-zero augmentation identifies it with the canonical gluing map. -/
theorem exists_cechComparisonSystem_comparison
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤) :
    ∃ comparison : ∀ q, TopCat.Sheaf.cechCohomologyFunctor U q ⟶
      Sheaf.functorH (Opens.grothendieckTopology X) q,
      comparison 0 =
        (TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv ≫
          (Sheaf.functorHZeroIso (Opens.grothendieckTopology X) isTerminalTop).inv := by
  sorry
end AlgebraicGeometry.Scheme.Modules
