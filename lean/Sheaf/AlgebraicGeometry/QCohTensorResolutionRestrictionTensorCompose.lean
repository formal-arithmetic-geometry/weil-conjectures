module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
open Scheme.Modules
noncomputable local instance trRestrictionTensorComposeMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Naturality of restriction tensor followed by maps on both factors. -/
theorem tensorResolutionRestrictionTensor_comp {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    {F F' G G' : Y.Modules} (f : F ⟶ F') (g : G ⟶ G')
    {H K : X.Modules}
    (a : (restrictFunctor j).obj F' ⟶ H)
    (b : (restrictFunctor j).obj G' ⟶ K) :
    (restrictFunctor j).map (f ⊗ₘ g) ≫
        (tensorResolutionRestrictionTensor j F' G').hom ≫ (a ⊗ₘ b) =
      (tensorResolutionRestrictionTensor j F G).hom ≫
        (((restrictFunctor j).map f ≫ a) ⊗ₘ
          ((restrictFunctor j).map g ≫ b)) := by
  rw [← Category.assoc, tensorResolutionRestrictionTensor_natural]
  rw [Category.assoc, tensorHom_comp_tensorHom]

end AlgebraicGeometry
