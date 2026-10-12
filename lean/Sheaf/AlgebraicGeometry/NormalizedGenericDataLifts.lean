module
public import Sheaf.AlgebraicGeometry.NormalizedGenericDataCore
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
/-- Geometric points lift through normalized generic data.
Source: Stacks Project, Tag 09Z6, algebraically closed extension argument.
(blueprint: new-normalized-generic-data-lifts).
Extend the residue-field map along the finite algebraic extension K and use
functoriality of Spec and the normalization factorization. -/
theorem normalized_generic_data_lifts
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (x : X)
    (Y : Scheme.{u}) (ν : Y ⟶ X) (hν : IsIntegralHom ν)
    (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ Y)
    (M : ModuleCat.{u + 1} Λ) (hM : Finite M)
    (hu : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))
    (he : Nonempty
      ((upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((upperStar (ModuleCat.{u + 1} Λ) ν).obj F) ≅
       (upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ((Scheme.SpecToEquivOfField Ω X) s).1 = x →
        ∃ w : Spec (.of Ω) ⟶ Spec (.of K), w ≫ g ≫ ν = s := by
  sorry
end AlgebraicGeometry.Etale
