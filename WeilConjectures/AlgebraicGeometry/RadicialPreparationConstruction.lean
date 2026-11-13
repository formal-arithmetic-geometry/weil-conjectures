/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import WeilConjectures.AlgebraicGeometry.ReducedFlatAffinePreparation
import WeilConjectures.AlgebraicGeometry.RadicialReducedFlatGenericFibre
import WeilConjectures.AlgebraicGeometry.RadicialPreparationFibreComparison
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-!
# Construction of a radicial preparation

Given an affine family of finite type whose generic fibre is geometrically irreducible, this file
constructs, over an affine neighbourhood of the generic point, a universal homeomorphism of
integral affine bases and a reduced family with geometrically reduced generic fibre that is
universally homeomorphic to the base change of the original family.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 051T](https://stacks.math.columbia.edu/tag/051T)
* [Stacks Project, Tag 052A](https://stacks.math.columbia.edu/tag/052A)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- Affine radicial preparation with a universal homeomorphism onto the original
base-changed family, before the final generic-flat shrinking. -/
theorem exists_radicial_preparation_construction
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    ∃ (U : T.Opens), η ∈ U ∧ IsAffineOpen U ∧
      ∃ (S Y : Scheme.{u}) (q : S ⟶ U.toScheme) (g : Y ⟶ S),
        IsAffine S ∧ IsIntegral S ∧ IsAffine Y ∧ IsReduced Y ∧
        IsUniversalHomeomorphism q ∧ LocallyOfFiniteType g ∧
        ∃ η' : S, IsGenericPoint η' Set.univ ∧ (q ≫ U.ι) η' = η ∧
          GeometricallyReduced (g.fiberToSpecResidueField η') ∧
          ∃ h : Y ⟶ pullback f (q ≫ U.ι),
            IsUniversalHomeomorphism h ∧ h ≫ pullback.snd f (q ≫ U.ι) = g := by
  let : GeometricallyIrreducible (f.fiberToSpecResidueField η) := hgeom
  have hηV : η ∈ V := by
    let : Surjective (f.fiberToSpecResidueField η) := inferInstance
    have hn : Nonempty (f.fiber η) := by
      obtain ⟨x, _⟩ :=
        (f.fiberToSpecResidueField η).surjective (Classical.choice inferInstance)
      exact ⟨x⟩
    obtain ⟨x⟩ := hn
    have hx : f (f.fiberι η x) = η := by
      have hx := (f.range_fiberι η).le ⟨x, rfl⟩
      exact hx
    exact hx ▸ himage ⟨f.fiberι η x, rfl⟩
  obtain ⟨U, hηU, hU, S₀, Z, q₀, h₀, hS₀, hiS₀, hZ, hrZ, hq₀, hh₀,
    hflat, hfp, η₀, hη₀, heη₀⟩ :=
    exists_reduced_flat_affine_preparation f V hV himage η hη hηV
  have : IsAffine S₀ := hS₀
  have : IsIntegral S₀ := hiS₀
  have : IsAffine Z := hZ
  have : IsReduced Z := hrZ
  have : IsUniversalHomeomorphism q₀ := hq₀
  have : IsUniversalHomeomorphism h₀ := hh₀
  let r₀ := q₀ ≫ U.ι
  let g₀ := h₀ ≫ pullback.snd f r₀
  have : Flat g₀ := hflat
  have : LocallyOfFinitePresentation g₀ := hfp
  have hgeom₀ : GeometricallyIrreducible (g₀.fiberToSpecResidueField η₀) := by
    apply (exists_radicial_preparation_fibre_comparison f r₀ h₀ η₀).mpr
    rw [heη₀]
    exact hgeom
  obtain ⟨S, q₁, hS, hiS, hq₁, η', hη', heη', hred⟩ :=
    exists_radicial_reduced_flat_generic_fibre g₀ η₀ hη₀ hgeom₀
  have : IsAffine S := hS
  have : IsIntegral S := hiS
  have : IsUniversalHomeomorphism q₁ := hq₁
  let P := pullback g₀ q₁
  let Y := P.nilradical.subscheme
  let a : Y ⟶ P := P.nilradical.subschemeι
  have : IsReduced Y :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism P).1
  have : Surjective a :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism P).2.2.1
  have : IsUniversalHomeomorphism a := inferInstance
  have : IsAffine P := inferInstance
  have : IsAffine Y := isAffine_of_isAffineHom a
  let g := a ≫ pullback.snd g₀ q₁
  let q := q₁ ≫ q₀
  refine ⟨U, hηU, hU, S, Y, q, g, hS, hiS, inferInstance, inferInstance,
    inferInstance, inferInstance, η', hη', ?_, hred, ?_⟩
  · change U.ι (q₀ (q₁ η')) = η
    rw [heη']
    exact heη₀
  · let e₁ := pullbackRightPullbackFstIso (pullback.snd f r₀) q₁ h₀
    let e₂ := pullbackLeftPullbackSndIso f r₀ q₁
    let k := e₁.inv ≫ pullback.snd h₀ (pullback.fst (pullback.snd f r₀) q₁) ≫ e₂.hom
    have hk : IsUniversalHomeomorphism k := inferInstance
    have hk_snd : k ≫ pullback.snd f (q₁ ≫ r₀) = pullback.snd g₀ q₁ := by
      simp [k, e₁, e₂, g₀]
    have hh : ∃ h : Y ⟶ pullback f (q₁ ≫ r₀),
        IsUniversalHomeomorphism h ∧ h ≫ pullback.snd f (q₁ ≫ r₀) = g := by
      refine ⟨a ≫ k, inferInstance, ?_⟩
      rw [Category.assoc, hk_snd]
    refine ⟨hh.choose, hh.choose_spec.1, ?_⟩
    change hh.choose ≫ pullback.snd f (q₁ ≫ q₀ ≫ U.ι) = g
    simpa [r₀, Category.assoc] using hh.choose_spec.2

end AlgebraicGeometry
