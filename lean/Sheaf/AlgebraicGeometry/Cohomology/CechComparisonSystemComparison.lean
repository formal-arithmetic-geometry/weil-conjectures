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
Proof: Use the displayed canonical natural transformation in degree zero and the zero
natural transformation in each positive degree. The normalization then holds definitionally.
No compatibility with connecting morphisms is asserted here. -/
theorem exists_cechComparisonSystem_comparison
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤) :
    ∃ comparison : ∀ q, TopCat.Sheaf.cechCohomologyFunctor U q ⟶
      Sheaf.functorH (Opens.grothendieckTopology X) q,
      comparison 0 =
        (TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv ≫
          (Sheaf.functorHZeroIso (Opens.grothendieckTopology X) isTerminalTop).inv := by
  let c₀ := (TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv ≫
    (Sheaf.functorHZeroIso (Opens.grothendieckTopology X) isTerminalTop).inv
  let comparison : ∀ q, TopCat.Sheaf.cechCohomologyFunctor U q ⟶
      Sheaf.functorH (Opens.grothendieckTopology X) q
    | 0 => c₀
    | _ + 1 => 0
  refine ⟨comparison, ?_⟩
  dsimp [comparison]
end AlgebraicGeometry.Scheme.Modules
