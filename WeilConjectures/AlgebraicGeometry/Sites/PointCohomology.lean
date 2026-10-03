/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Étale cohomology of the constant sheaf `ℤ` on the spectrum of a field

The étale cohomology of the spectrum of a field `K` is the Galois cohomology of
`Gal(Kˢᵉᵖ/K)`. For the constant sheaf `ℤ` this gives:

- in degree `1`, `H¹(Spec K_ét, ℤ) = Hom_cont(Gal(Kˢᵉᵖ/K), ℤ) = 0`, since a continuous
  homomorphism from a profinite group to the discrete torsion-free group `ℤ` has finite, hence
  trivial, image;
- in every positive degree, `Hⁿ(Spec k_ét, ℤ) = 0` for `k` separably closed, since then the
  Galois group is trivial.

For `k` separably closed we do not go through Galois cohomology: every étale covering of
`Spec k` has a section, so the global sections functor is exact and the constant sheaf `ℤ`,
which corepresents it, is a projective sheaf.

## Main statements

- `AlgebraicGeometry.Scheme.surjective_app_of_epi_of_isSepClosed`: for `k` separably closed,
  an epimorphism of abelian étale sheaves on `Spec k` is surjective on global sections.
- `AlgebraicGeometry.Scheme.subsingleton_H_constantSheaf_of_isSepClosed`:
  `H^q(Spec k_ét, ℤ) = 0` for `q ≥ 1` and `k` separably closed.
- `AlgebraicGeometry.Scheme.subsingleton_H_one_constantSheaf_of_isField`:
  `H¹(Spec K_ét, ℤ) = 0` for every field `K`. The proof is `sorry`.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

section IsSepClosed

variable (k : Type u) [Field k] [IsSepClosed k]

/-- The terminal object `𝟙 : Spec k ⟶ Spec k` of the small étale site of `Spec k`. -/
local notation "𝟙ₑ" => MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of k)))
  (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of k)))

/-- Over a separably closed field `k`, every covering sieve of `Spec k` in the small étale site
contains the identity: some member of an étale covering is nonempty, and a nonempty étale
`k`-scheme has a `k`-point. -/
lemma id_mem_of_mem_smallEtaleTopology_of_isSepClosed (R : Sieve 𝟙ₑ)
    (hR : R ∈ (Spec (.of k)).smallEtaleTopology 𝟙ₑ) : R.arrows (𝟙 _) := by
  obtain ⟨𝒰, h𝒰, p, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hR
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (default : Spec (.of k))
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f j) (𝟙 _) y (by rw [hy]; rfl)
  have hmem : R.arrows ((𝒰.f j).asOverProp _) := hle _ _ (Presieve.ofArrows.mk j)
  convert R.downward_closed hmem (MorphismProperty.Over.homMk (A := 𝟙ₑ)
    (B := (𝒰.X j).asOverProp _ (p j)) l (by
      change l ≫ (𝒰.X j ↘ _) = 𝟙 _
      rw [← comp_over (𝒰.f j), ← Category.assoc, hl, Category.id_comp]
      rfl))
  exact MorphismProperty.Over.Hom.ext hl.symm

/-- Over a separably closed field `k`, an epimorphism of abelian étale sheaves on `Spec k` is
surjective on global sections. -/
lemma surjective_app_of_epi_of_isSepClosed
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op 𝟙ₑ)) := by
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) φ).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := id_mem_of_mem_smallEtaleTopology_of_isSepClosed k _
    (Presheaf.imageSieve_mem (Spec (.of k)).smallEtaleTopology φ.hom (U := op 𝟙ₑ) s)
  exact ⟨t, ht.trans (by simp)⟩

instance preservesEpimorphisms_sheafSections_of_isSepClosed :
    ((sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op 𝟙ₑ)).PreservesEpimorphisms where
  preserves φ _ := (AddCommGrpCat.epi_iff_surjective _).2
    (surjective_app_of_epi_of_isSepClosed k φ)

/-- Over a separably closed field `k`, the constant sheaf `ℤ` on the small étale site of
`Spec k` is projective: it corepresents the global sections functor, which is exact. -/
instance projective_constantSheaf_of_isSepClosed :
    Projective ((constantSheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) := by
  have hT : Limits.IsTerminal 𝟙ₑ := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  exact @Adjunction.map_projective _ _ _ _ _ _ (constantSheafAdj _ _ hT)
    (preservesEpimorphisms_sheafSections_of_isSepClosed k) _ AddCommGrpCat.projective_of_uliftInt

/-- **Cohomology of `ℤ` on a geometric point.** For a separably closed field `k` (in
particular an algebraically closed one), `H^q(Spec k_ét, ℤ) = 0` for all `q ≥ 1`. The
blueprint argues via the equivalence of étale sheaves on `Spec k` with discrete Galois modules,
the Galois group being trivial; we use directly that the constant sheaf `ℤ` is projective
(`AlgebraicGeometry.Scheme.projective_constantSheaf_of_isSepClosed`).
(blueprint: `lem-sc-point-z-cohomology`) -/
theorem subsingleton_H_constantSheaf_of_isSepClosed (q : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (Spec (.of k)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) (q + 1)) :=
  Abelian.Ext.subsingleton_of_projective _ _ _

end IsSepClosed

/-- **`H¹` of `ℤ` on the spectrum of a field vanishes.** For every field `K`,
`H¹(Spec K_ét, ℤ) = Hom_cont(Gal(Kˢᵉᵖ/K), ℤ) = 0`: étale cohomology of `Spec K` is Galois
cohomology, and a continuous homomorphism from the profinite group `Gal(Kˢᵉᵖ/K)` to the
discrete group `ℤ` has finite image, hence is trivial. The proof is `sorry`; it needs the
comparison of étale cohomology of a field with Galois cohomology. -/
theorem subsingleton_H_one_constantSheaf_of_isField (K : CommRingCat.{u}) (hK : IsField K) :
    Subsingleton (Sheaf.H ((constantSheaf (Spec K).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) 1) :=
  sorry

end AlgebraicGeometry.Scheme
