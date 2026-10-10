/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

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
      (φ : ∀ a, (W a).toScheme ⟶ U), ⨆ a, W a = ⊤ ∧ ∀ a, φ a ≫ u = (W a).ι ≫ r :=
  sorry

/-- The case of `AlgebraicGeometry.Scheme.exists_finite_surjective_refinement_of_etale` where `u`
is already finite: take `r = u` and the single open `U`. This is the base case of the induction in
Stacks 09Z0. -/
theorem Scheme.exists_finite_surjective_refinement_of_etale_of_isFinite {U T : Scheme.{u}}
    (u : U ⟶ T) [Etale u] [Surjective u] [IsFinite u] :
    ∃ (T' : Scheme.{u}) (r : T' ⟶ T) (_ : IsFinite r) (_ : LocallyOfFinitePresentation r)
      (_ : Surjective r) (J : Type) (_ : Finite J) (W : J → T'.Opens)
      (φ : ∀ a, (W a).toScheme ⟶ U), ⨆ a, W a = ⊤ ∧ ∀ a, φ a ≫ u = (W a).ι ≫ r :=
  ⟨U, u, inferInstance, inferInstance, inferInstance, Unit, inferInstance, fun _ ↦ ⊤,
    fun _ ↦ (⊤ : U.Opens).ι, by simp, fun _ ↦ rfl⟩

end AlgebraicGeometry
