/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.NormalizedGenericDataWithFactorization
import WeilConjectures.AlgebraicGeometry.NormalizedGenericDataLifts

/-!
# Normalized generic trivialization data

Source: Stacks Project, Tag 09Z6, generic trivialization and normalization, using Tag 09Z5.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Generic trivialization on an integral model, together with lifting of geometric points.

Source: Stacks Project, Tag 09Z6, proof
of (1), the paragraph from the reduced closure through the generic inclusion, transferred
to (3); Tag 09Z5. -/
theorem exists_constructible_module_normalized_generic_data
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
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
          ((Scheme.SpecToEquivOfField Ω X) s).1 = x →
            ∃ w : Spec (.of Ω) ⟶ Spec (.of K), w ≫ g ≫ ν = s := by
  obtain ⟨Y, ν, hν, K, hK, g, M, hM, hu, he, a, ha, hcomp⟩ :=
    exists_constructible_module_normalized_generic_data_with_factorization Λ F hF x
  refine ⟨Y, ν, hν, K, hK, g, M, hM, hu, he, ?_⟩
  exact normalized_generic_data_lifts Λ F hF x Y ν hν K hK g a ha hcomp M hM hu he

end AlgebraicGeometry.Etale
