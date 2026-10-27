/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
import Sheaf.AlgebraicGeometry.QuasiAffineOpenPrincipalComparisonCover
import Sheaf.AlgebraicGeometry.AffinePrincipalAffinizationIsomorphism

/-! # Cartesian affinization square for an open inside a quasi-affine scheme

Source: Stacks Project, `properties.tex`, Tag 0ARY, lemma-cartesian-diagram-quasi-affine
(blueprint: lem-a1-quasi-affine-open-affinization-square).

The canonical affinization maps of a quasi-affine scheme and of a quasi-affine open
subscheme form the cartesian square specified by Tag 0ARY.
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/--
For an open immersion between quasi-affine schemes, the square formed by the two
canonical maps to spectra of global sections is cartesian.

Source: Stacks Project, `properties.tex`, Tag 0ARY, lemma-cartesian-diagram-quasi-affine
(blueprint: lem-a1-quasi-affine-open-affinization-square).
The proof follows Tag 0ARY: identify the open image in the target affinization by
principal opens, use the localization description of sections on each principal
open, and take their union.  The resulting inverse-image open is the source, and
its universal property is the displayed pullback property.
-/
theorem isPullback_toSpecΓ_of_isOpenImmersion
    {U V : Scheme.{u}} (u : U ⟶ V) [IsOpenImmersion u]
    [U.IsQuasiAffine] [V.IsQuasiAffine] :
    IsPullback U.toSpecΓ (𝟙 U) (Spec.map u.appTop) (u ≫ V.toSpecΓ) := by
  obtain ⟨_, hcomm, _, hcover, hcharts, _⟩ :=
    quasiAffine_open_principal_comparison_cover u
  have himage : Spec.map u.appTop ⁻¹ᵁ (u ≫ V.toSpecΓ).opensRange =
      U.toSpecΓ.opensRange := by
    ext x
    change Spec.map u.appTop x ∈ Set.range (u ≫ V.toSpecΓ) ↔
      x ∈ Set.range U.toSpecΓ
    constructor
    · intro hx
      rw [hcover] at hx
      obtain ⟨g, hxg⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hg, hxg⟩ := Set.mem_iUnion.mp hxg
      obtain ⟨_, _, _, _, hpre, _, haff⟩ := hcharts g hg
      have hxf : x ∈ PrimeSpectrum.basicOpen (u.appTop g) := by
        rw [← hpre]
        exact hxg
      let e := U.toSpecΓ.resLE (PrimeSpectrum.basicOpen (u.appTop g))
        (U.basicOpen (u.appTop g)) (U.toSpecΓ_preimage_basicOpen _).ge
      have : IsIso e := (affine_principal_affinization_isomorphism U
        (u.appTop g) haff).2.1
      obtain ⟨y, hy⟩ := e.homeomorph.surjective ⟨x, hxf⟩
      refine ⟨y.1, ?_⟩
      exact (Hom.coe_resLE_apply _ _ y).symm.trans (congrArg Subtype.val hy)
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      exact (congrArg (fun f : U ⟶ Spec Γ(V, ⊤) => f y) hcomm).symm
  exact (IsOpenImmersion.isPullback (𝟙 U) U.toSpecΓ (u ≫ V.toSpecΓ)
    (Spec.map u.appTop) (by simpa using hcomm) himage).flip

end AlgebraicGeometry.Scheme
