/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.ConstructibleSheaf.FinitePushforward
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleNoetherianDescent
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian

/-!
# Finite-pushforward embeddings of constructible module sheaves

Source: Stacks Project, Etale Cohomology, Lemma 09Z7 (3).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A constructible sheaf over a finite commutative coefficient ring on a quasi-compact,
quasi-separated scheme embeds into a finite biproduct of direct images of constant finite
module sheaves along finite, locally finitely presented morphisms (Stacks, Tag 09Z7). -/
theorem finite_pushforward_embedding_of_isConstructibleEtaleModuleSheaf
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i : Fin n, Y i ⟶ X),
      (∀ i : Fin n, IsFinite (f i)) ∧
      (∀ i : Fin n, LocallyOfFinitePresentation (f i)) ∧
      ∃ (M : Fin n → ModuleCat.{u + 1} Λ), (∀ i : Fin n, Finite (M i)) ∧
        ∃ (φ : F ⟶ ⨁ fun i : Fin n ↦
          (lowerStar (ModuleCat.{u + 1} Λ) (f i)).obj
            ((constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))),
          Mono φ := by
  obtain ⟨X', hX', ν, F', hF', e⟩ := exists_noetherian_descent Λ F hF
  have : IsNoetherian X' := hX'
  obtain ⟨n, Y, f, hf, M, hM, φ, hφ⟩ :=
    exists_mono_biproduct_lowerStar_of_isNoetherian_etaleModule Λ F' hF'
  have : ∀ i, IsFinite (f i) := hf
  have : ∀ i, LocallyOfFinitePresentation (f i) := fun _ ↦ inferInstance
  obtain ⟨Y', g, hg, hgfp, φ', hφ'⟩ :=
    exists_mono_biproduct_lowerStar_upperStar Λ ν F' Y f M φ
  exact ⟨n, Y', g, hg, hgfp, M, hM, e.some.inv ≫ φ', inferInstance⟩

end AlgebraicGeometry.Etale
