/- helper uniqueness -/
module
public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheafExists
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Canonical section equations determine the inverse-image morphism uniquely.
(blueprint: new-etaleSetInverseImageConstantSheaf-uniqueness) -/
theorem etaleSetInverseImageConstantSheaf_unique
    (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u)
    (γ : etaleSetInverseImageConstantSheafHom U V v E)
    (hγ : etaleSetInverseImageConstantSheafCondition U V v E γ) :
    ∀ γ' : etaleSetInverseImageConstantSheafHom U V v E,
      etaleSetInverseImageConstantSheafCondition U V v E γ' → γ' = γ := by
  sorry
end AlgebraicGeometry
