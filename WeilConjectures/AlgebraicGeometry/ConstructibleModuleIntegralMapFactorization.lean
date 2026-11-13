/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.IntegralConstantModulePushforwardColimit
import WeilConjectures.ConstructibleSheaf.FinitePushforward

/-!
# Finite-stage factorization of maps to integral constant pushforwards

Source: Stacks Project, Tag 09Z6, proof using Tags 09Z1 and 09Z4.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A map from a constructible module sheaf to an integral pushforward of a finite constant
module factors through a finite pushforward of that same constant module.

Source: Stacks Project, Tag 09Z6, final paragraph of the proof of (1), transferred to (3),
using Tags 09YZ, 09Z1 and 09Z4. -/
theorem exists_finite_lowerStar_factorization
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    {Y : Scheme.{u}} (ν : Y ⟶ X) [IsIntegralHom ν]
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (φ : F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X), IsFinite f ∧
      ∃ (ψ : F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
        (κ : (lowerStar (ModuleCat.{u + 1} Λ) f).obj
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ⟶
          (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)),
        ψ ≫ κ = φ := by
  classical
  obtain ⟨S, hS⟩ := hF
  have : ∀ i : Fin S.n, IsImmersion (S.immersion i) := S.isImmersion
  have : Scheme.IsConstructibleSheaf F :=
    Scheme.IsConstructibleSheaf.of_noetherianSpace F S.stratum S.isLocallyClosed_stratum
      S.iUnion_stratum_eq_univ S.pairwise_disjoint_stratum S.immersion S.range_immersion
      (fun i ↦ (Scheme.finite_locally_constant_module_values_iff _).1.mp (hS i))
  have : IsFinitelyPresentable.{u} F := isFinitelyPresentable_of_isConstructibleSheaf Λ F
  obtain ⟨I, hI, hfilter, Z, f, hf, D, e, η, hc⟩ :=
    exists_filtered_colimit_finite_lowerStar_constant Λ ν M
  obtain ⟨i, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc.some φ
  let ei := (e i).some
  refine ⟨Z i, f i, hf i, p ≫ ei.hom, ei.inv ≫ η.app i, ?_⟩
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hp

end AlgebraicGeometry.Etale
