/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.CategoryTheory.Sites.CechComplexModule

/-!
# Injective étale sheaves of modules are acyclic as abelian sheaves

An injective presheaf of `Λ`-modules is a retract of its cofree presheaf, so its Čech complexes
are exact in positive degrees (`CategoryTheory.Presheaf.exactAt_cechComplex_forget₂_of_injective`).
By the Čech criterion, the underlying abelian sheaf of an injective étale sheaf of `Λ`-modules on
a quasi-compact quasi-separated scheme has no higher cohomology. This compares the cohomology of
sheaves of `Λ`-modules with that of their underlying abelian sheaves.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_H_forget₂_of_injective`: on a quasi-compact
  quasi-separated scheme, the underlying abelian sheaf of an injective étale sheaf of
  `Λ`-modules has no higher cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

open Presheaf

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- On a quasi-compact quasi-separated scheme, the underlying abelian sheaf of an injective
étale sheaf of `Λ`-modules has no higher cohomology. -/
theorem subsingleton_H_forget₂_of_injective (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J]
    (q : ℕ) :
    Subsingleton (Sheaf.H ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J) (q + 1)) := by
  have : Injective J.obj := (sheafificationAdjunction _ _).map_injective J inferInstance
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
  let B : X.Etale → Prop := fun W ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left
  have hcov (V : X.Etale) (hV : B V) (R : Sieve V) (hR : R ∈ X.smallEtaleTopology V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology V := by
    obtain ⟨_, _⟩ := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
    refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
      (ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
    refine compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
    have := hU (y l)
    exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
      inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩
  have hF (V : X.Etale) {n : ℕ} (U : Fin n → Over V) (q : ℕ) :
      ((cechComplex U).obj ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J).obj).ExactAt (q + 1) :=
    exactAt_cechComplex_forget₂_of_injective U J.obj q
  exact Sheaf.subsingleton_H_succ_of_exactAt_cechComplex hT B
    ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ hcov _ (fun V _ _ U _ _ q ↦ hF V U q) q

end AlgebraicGeometry.Scheme
