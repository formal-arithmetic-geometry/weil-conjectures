/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.Approximation
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.Bound

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

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Reduction to an affine source** (the first step of Stacks 09Z0). For a surjective étale
`u : U ⟶ T` with `T` quasi-compact, finitely many affine opens of `U` already have images
covering `T`, since images of opens under the étale `u` are open; their disjoint union `U'` is
affine, with a morphism `i : U' ⟶ U` such that `i ≫ u` is still étale and surjective. -/
theorem Scheme.exists_isAffine_etale_surjective_comp {U T : Scheme.{u}} (u : U ⟶ T) [Etale u]
    [Surjective u] [CompactSpace T] :
    ∃ (U' : Scheme.{u}) (i : U' ⟶ U), IsAffine U' ∧ Etale (i ≫ u) ∧ Surjective (i ≫ u) := by
  classical
  have hopen (V : U.affineOpens) : IsOpen (u.base '' (V : Set U)) :=
    u.isOpenMap _ V.1.isOpen
  have hcov : (Set.univ : Set T) ⊆ ⋃ V : U.affineOpens, u.base '' (V : Set U) := by
    intro t _
    obtain ⟨x, rfl⟩ := u.surjective t
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : U.Opens) from trivial)
    exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, x, hxV, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  let Y : s → Scheme.{u} := fun V ↦ (V.1.1 : U.Opens).toScheme
  have (V : s) : IsAffine (Y V) := V.1.2
  let i : ∐ Y ⟶ U := Sigma.desc fun V : s ↦ (V.1.1 : U.Opens).ι
  have hi : i ≫ u = Sigma.desc fun V : s ↦ (V.1.1 : U.Opens).ι ≫ u := by
    ext1 V
    simp only [i, Sigma.ι_desc_assoc]
    exact (Sigma.ι_desc (fun V : s ↦ (V.1.1 : U.Opens).ι ≫ u) V).symm
  refine ⟨∐ Y, i, inferInstance, ?_, ⟨fun t ↦ ?_⟩⟩
  · rw [hi]
    exact IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  · obtain ⟨V, hV, x, hx, rfl⟩ : ∃ V ∈ s, ∃ x ∈ (V.1 : Set U), u.base x = t := by
      obtain ⟨V, hV, ht⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ t))
      obtain ⟨x, hx, rfl⟩ := ht
      exact ⟨V, hV, x, hx, rfl⟩
    refine ⟨(Sigma.ι Y ⟨V, hV⟩).base ⟨x, hx⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Sigma.ι_desc]
    rfl

/-- **Finite refinement of a surjective étale morphism with affine source** (Stacks 09Z0 for an
affine `U`). The geometric fibres of `u` are bounded, since by Zariski's main theorem `u` is open
in a finite `T`-scheme (`Scheme.Hom.exists_card_lifts_le_of_isFinite`). The induction on this
bound gives finitely many finite morphisms to `T` that factor through `u` Zariski locally
(`Scheme.Hom.hasFiniteRefinement_of_hasGeometricFibersCardLE`); we make them of finite
presentation (`Scheme.Hom.exists_locallyOfFinitePresentation_locallyFactorsThrough`) and take
their disjoint union. -/
theorem Scheme.exists_finite_surjective_refinement_of_etale_of_isAffine {U T : Scheme.{u}}
    (u : U ⟶ T) [IsAffine U] [Etale u] [Surjective u] [CompactSpace T] [QuasiSeparatedSpace T] :
    ∃ (T' : Scheme.{u}) (r : T' ⟶ T) (_ : IsFinite r) (_ : LocallyOfFinitePresentation r)
      (_ : Surjective r) (J : Type) (_ : Finite J) (W : J → T'.Opens)
      (φ : ∀ a, (W a).toScheme ⟶ U), ⨆ a, W a = ⊤ ∧ ∀ a, φ a ≫ u = (W a).ι ≫ r := by
  have : IsSeparated u := by
    have : IsSeparated (u ≫ T.toSpecΓ) := IsSeparated.of_isAffineHom _
    exact IsSeparated.of_comp u T.toSpecΓ
  -- the geometric fibres of `u` are bounded
  obtain ⟨Y₀, j₀, p₀, _, _, _, hjp₀⟩ := u.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  obtain ⟨n, hn⟩ := p₀.exists_card_lifts_le_of_isFinite
  have hd : u.HasGeometricFibersCardLE n := fun Ω _ _ g ↦
    (ENat.card_le_card_of_injective (f := fun s : {s // s ≫ u = g} ↦
      (⟨s.1 ≫ j₀, by rw [Category.assoc, hjp₀, s.2]⟩ : {s // s ≫ p₀ = g}))
      fun s₁ s₂ h ↦ Subtype.ext ((cancel_mono j₀).1 congr($h.1))).trans (hn Ω g)
  -- the induction, and finite presentation
  obtain ⟨K, _, Tk, r, _, hsurj, hloc⟩ := u.hasFiniteRefinement_of_hasGeometricFibersCardLE n hd
  choose T' r' _ _ hr' hloc' using fun k ↦
    (r k).exists_locallyOfFinitePresentation_locallyFactorsThrough u (hloc k)
  let R : ∐ T' ⟶ T := Sigma.desc r'
  have : LocallyOfFinitePresentation R := IsZariskiLocalAtSource.sigmaDesc fun k ↦ inferInstance
  have : Surjective R := Surjective.sigmaDesc_of_union_range_eq_univ
    (Set.eq_univ_of_forall fun x ↦ by
      obtain ⟨k, t, ht⟩ := hsurj x
      exact Set.mem_iUnion.2 ⟨k, hr' k ⟨t, ht⟩⟩)
  have : CompactSpace ↥(∐ T') := QuasiCompact.compactSpace_of_compactSpace R
  have hlocR (z : ↥(∐ T')) : ∃ (O : (∐ T').Opens) (_ : z ∈ O) (φ : O.toScheme ⟶ U),
      φ ≫ u = O.ι ≫ R := by
    obtain ⟨k, z', hz⟩ := (sigmaOpenCover T').exists_eq z
    rw [sigmaOpenCover_f] at hz
    subst hz
    obtain ⟨O, hO, φ, hφ⟩ := hloc' k z'
    refine ⟨Sigma.ι T' k ''ᵁ O, ⟨z', hO, rfl⟩, ((Sigma.ι T' k).isoImage O).inv ≫ φ, ?_⟩
    rw [Category.assoc, hφ, Iso.inv_comp_eq, ← Category.assoc, Scheme.Hom.isoImage_hom_ι,
      Category.assoc, Sigma.ι_desc]
  choose O hO φ hφ using hlocR
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun z ↦ (O z : Set ↥(∐ T')))
    (fun z ↦ (O z).2) fun z _ ↦ Set.mem_iUnion.2 ⟨z, hO z⟩
  refine ⟨∐ T', R, inferInstance, inferInstance, inferInstance, Fin s.card, inferInstance,
    fun a ↦ O (s.equivFin.symm a), fun a ↦ φ _, eq_top_iff.2 fun z _ ↦ ?_, fun a ↦ hφ _⟩
  obtain ⟨z₀, hz₀, hz⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ z))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨s.equivFin ⟨z₀, hz₀⟩, by simpa using hz⟩

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
  -- replace `U` by a finite disjoint union of affine opens
  obtain ⟨U', i, _, _, _⟩ := Scheme.exists_isAffine_etale_surjective_comp u
  -- the case of an affine source: the induction on the degree of the geometric fibres of
  -- Stacks 09Z0, through Zariski's main theorem, and finite approximation
  obtain ⟨T', r, h₁, h₂, h₃, J, hJ, W, φ, hW, hφ⟩ :
      ∃ (T' : Scheme.{u}) (r : T' ⟶ T) (_ : IsFinite r) (_ : LocallyOfFinitePresentation r)
        (_ : Surjective r) (J : Type) (_ : Finite J) (W : J → T'.Opens)
        (φ : ∀ a, (W a).toScheme ⟶ U'), ⨆ a, W a = ⊤ ∧ ∀ a, φ a ≫ i ≫ u = (W a).ι ≫ r :=
    Scheme.exists_finite_surjective_refinement_of_etale_of_isAffine (i ≫ u)
  exact ⟨T', r, h₁, h₂, h₃, J, hJ, W, fun a ↦ φ a ≫ i, hW, fun a ↦ by
    rw [Category.assoc, hφ a]⟩

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
