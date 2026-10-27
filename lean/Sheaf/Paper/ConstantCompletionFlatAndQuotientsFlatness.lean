module
public import Sheaf.Paper.ConstantCompletionBasic
/-! Flatness component of constant coefficient completion.
Source: Stacks Project, Tag 093M (blueprint: lem-weil-pbc-constant-completion-equivalence).
(blueprint: new-h2-constant-completion-flatness)
The sectionwise adic algebra limit theorem applied to the finite quotient tower proves
that the completed coefficient algebra is flat over the constant coefficient sheaf. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]
theorem flat_and_quotients_flatness (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    SheafOfModules.IsFlat
      ((res (coefficientMap J A I)).obj (SheafOfModules.unit
        (siteModuleRings (completed J A I)))) := by
  sorry
end CategoryTheory.ConstantCompletion
