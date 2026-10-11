/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Finite refinement of a surjective étale morphism

A surjective étale morphism `u : U ⟶ T` onto a quasi-compact and quasi-separated scheme is
refined, Zariski locally, by a finite surjective morphism: there is a finite, finitely
presented, surjective `r : T' ⟶ T` and a finite open covering `T' = ⋃ₐ Wₐ` such that every
`r|_{Wₐ}` factors through `u`. This is the finite-refinement input of the degree-zero
comparison over a henselian pair.

## Main statements

- `AlgebraicGeometry.Scheme.exists_finite_surjective_refinement_of_etale`.

## References

- Stacks Project, Lemma 37.45.7, <https://stacks.math.columbia.edu/tag/09Z0>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Finite refinement, affine source.** The case of
`AlgebraicGeometry.Scheme.exists_finite_surjective_refinement_of_etale` in which `U` is affine,
so that `u` is quasi-compact and separated. This is where the proof of Stacks 09Z0 starts: it
inducts on a bound for the geometric fibres of `u`, using Zariski's main theorem and a limit
argument. -/
theorem Scheme.exists_finite_surjective_refinement_of_etale_of_isAffine {U T : Scheme.{u}}
    (u : U ⟶ T) [Etale u] [Surjective u] [IsAffine U] [CompactSpace T]
    [QuasiSeparatedSpace T] :
    ∃ (T' : Scheme.{u}) (r : T' ⟶ T) (_ : IsFinite r) (_ : LocallyOfFinitePresentation r)
      (_ : Surjective r) (J : Type) (_ : Finite J) (W : J → T'.Opens)
      (φ : ∀ a, (W a).toScheme ⟶ U), ⨆ a, W a = ⊤ ∧ ∀ a, φ a ≫ u = (W a).ι ≫ r :=
  sorry

/-- **Finite refinement of a surjective étale morphism.** Let `u : U ⟶ T` be surjective and
étale, with `T` quasi-compact and quasi-separated. There are a finite, finitely presented,
surjective morphism `r : T' ⟶ T`, a finite open covering `T' = ⋃ₐ Wₐ` and `T`-morphisms
`φₐ : Wₐ ⟶ U` with `φₐ ≫ u = r|_{Wₐ}`: the morphism `r` factors through `u` Zariski locally on
`T'`. The proof (Stacks 09Z0) inducts on a bound for the geometric fibres of `u`, using
Zariski's main theorem and a limit argument.
(blueprint: `lemma-weil-pbc-finite-refinement-etale-cover`) -/
@[stacks 09Z0]
theorem Scheme.exists_finite_surjective_refinement_of_etale {U T : Scheme.{u}} (u : U ⟶ T)
    [Etale u] [Surjective u] [CompactSpace T] [QuasiSeparatedSpace T] :
    ∃ (T' : Scheme.{u}) (r : T' ⟶ T) (_ : IsFinite r) (_ : LocallyOfFinitePresentation r)
      (_ : Surjective r) (J : Type) (_ : Finite J) (W : J → T'.Opens)
      (φ : ∀ a, (W a).toScheme ⟶ U), ⨆ a, W a = ⊤ ∧ ∀ a, φ a ≫ u = (W a).ι ≫ r := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun V : U.affineOpens ↦ u.base '' (V : Set U)) (fun V ↦ u.isOpenMap _ V.1.2)
    (fun t _ ↦ by
      obtain ⟨x, rfl⟩ := u.surjective t
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        U.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨_, hV⟩, x, hxV, rfl⟩)
  let g : s → Scheme.{u} := fun i ↦ ((i : U.affineOpens) : U.Opens).toScheme
  have : ∀ i, IsAffine (g i) := fun i ↦ i.1.2
  let ι : ∐ g ⟶ U := Limits.Sigma.desc fun (i : s) ↦ ((i : U.affineOpens) : U.Opens).ι
  have hι : ι ≫ u = Limits.Sigma.desc fun (i : s) ↦ ((i : U.affineOpens) : U.Opens).ι ≫ u := by
    ext i : 1
    simp only [ι, Limits.Sigma.ι_desc_assoc]
    exact (Limits.Sigma.ι_desc (fun (i : s) ↦ ((i : U.affineOpens) : U.Opens).ι ≫ u) i).symm
  have : Etale (ι ≫ u) := by
    rw [hι]
    exact IsZariskiLocalAtSource.sigmaDesc fun i ↦ inferInstance
  have : Surjective (ι ≫ u) := by
    rw [hι]
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun t ↦ ?_)
    obtain ⟨V, hV, x, hx, rfl⟩ : ∃ V ∈ s, ∃ x ∈ (V : Set U), u.base x = t := by
      simpa using hs (Set.mem_univ t)
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, ⟨x, hx⟩, rfl⟩
  obtain ⟨T', r, h₁, h₂, h₃, J, hJ, W, φ, hW, hφ⟩ :=
    exists_finite_surjective_refinement_of_etale_of_isAffine (ι ≫ u)
  exact ⟨T', r, h₁, h₂, h₃, J, hJ, W, fun a ↦ φ a ≫ ι, hW,
    fun a ↦ by rw [Category.assoc, hφ a]⟩

end AlgebraicGeometry
