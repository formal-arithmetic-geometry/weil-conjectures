/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField

/-!
# Global sections on the spectrum of an algebraically closed field are exact

Let `K` be an algebraically closed field. Every pro-étale covering family of `Spec K` has a
member with a section (`AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale`), so every
covering sieve of the terminal object of the small pro-étale site of `Spec K` is the maximal
sieve. Hence an epimorphism of pro-étale sheaves on `Spec K`, being locally surjective, is
surjective on global sections: the global sections functor preserves epimorphisms.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.id_mem_of_mem_topology_of_isAlgClosed`: a covering sieve of
  the terminal object of the small pro-étale site of `Spec K` contains the identity.
- `AlgebraicGeometry.ProEtale.surjective_app_of_epi_of_isAlgClosed`: an epimorphism of
  `ℓ`-adic pro-étale sheaves on `Spec K` is surjective on global sections.
- `AlgebraicGeometry.ProEtale.preservesEpimorphisms_Γ_of_isAlgClosed`: the global sections
  functor on `ℓ`-adic pro-étale sheaves on `Spec K` preserves epimorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A covering sieve of the terminal object `Spec K` of the small pro-étale site of the spectrum
of an algebraically closed field `K` contains the identity: a member `f : V ⟶ Spec K` of a
pro-étale covering family with `V` nonempty has a section `σ`, and `σ ≫ f = 𝟙`. -/
lemma Scheme.ProEt.id_mem_of_mem_topology_of_isAlgClosed
    {S : Sieve (Scheme.ProEt.mk (𝟙 (Spec (.of K))))}
    (hS : S ∈ Scheme.ProEt.topology (Spec (.of K)) _) : S (𝟙 _) := by
  obtain ⟨R, hR, hRS⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  have hR' := (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from
    inf_le_right) _ hR
  obtain ⟨Y, g, hg, x, -⟩ := hR'.1 (IsLocalRing.closedPoint K)
  obtain ⟨hg⟩ := hg
  obtain @⟨V, f, hf⟩ := hg
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale V.hom x
  have hσ : σ ≫ V.hom = (Scheme.ProEt.mk (𝟙 (Spec (.of K)))).hom := hσ
  have : S (MorphismProperty.Over.homMk (A := Scheme.ProEt.mk (𝟙 (Spec (.of K)))) σ hσ ≫ f) :=
    S.downward_closed (hRS _ _ hf) _
  convert this
  exact (Scheme.ProEt.isTerminalMkId _).hom_ext _ _

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- An epimorphism of `ℓ`-adic pro-étale sheaves on the spectrum of an algebraically closed field
`K` is surjective on sections over the terminal object `Spec K`: it is locally surjective, and
every covering sieve of `Spec K` is the maximal sieve. -/
lemma surjective_app_of_epi_of_isAlgClosed
    {F G : Sheaf (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)} (φ : F ⟶ G)
    [Epi φ] : Function.Surjective (φ.hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) := by
  have := (Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := Scheme.ProEt.id_mem_of_mem_topology_of_isAlgClosed
    (Presheaf.imageSieve_mem (Scheme.ProEt.topology _) φ.hom s)
  exact ⟨t, by simpa using ht⟩

/-- The global sections functor on `ℓ`-adic pro-étale sheaves on the spectrum of an
algebraically closed field preserves epimorphisms. -/
instance preservesEpimorphisms_Γ_of_isAlgClosed :
    (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).PreservesEpimorphisms
    where
  preserves {F G} φ _ := by
    let e := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology (Spec (.of K)))
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId (Spec (.of K)))
    have h : (Sheaf.Γ _ _).map φ =
        e.hom.app F ≫ ((sheafSections _ _).obj _).map φ ≫ e.inv.app G := by
      rw [← reassoc_of% (e.hom.naturality φ)]
      simp
    have : Epi (((sheafSections (Scheme.ProEt.topology (Spec (.of K)))
        (WeilCoefficients.{u} l)).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))).map φ) :=
      (ModuleCat.epi_iff_surjective _).2 (surjective_app_of_epi_of_isAlgClosed φ)
    rw [h]
    infer_instance

end ProEtale

end AlgebraicGeometry
