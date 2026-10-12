module
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
/-- Core normalized generic data, omitting the geometric lifting clause.
Source: Stacks Project, Tag 09Z6, normalization and generic trivialization.
(blueprint: new-normalized-generic-data-core).
The construction pulls back to the residue field, trivializes after a finite
separable extension, and normalizes that extension over the reduced closure. -/
theorem exists_constructible_module_normalized_generic_data_core
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (x : X) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X), IsIntegralHom ν ∧
      ∃ (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ Y)
        (M : ModuleCat.{u + 1} Λ), Finite M ∧
        IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ∧
        Nonempty
          ((upperStar (ModuleCat.{u + 1} Λ) g).obj
            ((upperStar (ModuleCat.{u + 1} Λ) ν).obj F) ≅
           (upperStar (ModuleCat.{u + 1} Λ) g).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  sorry
end AlgebraicGeometry.Etale
