/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Étale-local normal form at a smooth point

Source: Stacks Project, Tags 01V5 and 054L
(blueprint: sbc-thm-etale-local-normal-form).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 054L (blueprint: sbc-thm-etale-local-normal-form).
A morphism smooth at `x` factors on affine neighbourhoods through an étale map to affine
space. The hypothesis expands smoothness at a point exactly as in Tag 01V5(1); it imposes
no finite-presentation condition away from the chosen chart.

Proof plan:
1. Choose the affine smooth chart in the hypothesis. Its point `x` corresponds to a prime
   by `lem-weil-pbc-affine-open-spec-points`.
2. By `lem-weil-pbc-smooth-ring-map-locally-standard-smooth`, choose a principal neighbourhood
   on which the algebra is standard smooth. The section-localization and point-membership
   assertions are `lem-weil-pbc-affine-open-section-vanishing-prime`.
3. Transport the standard smooth presentation along this localization identification as
   an algebra over the target's sections. Its Jacobian determinant remains a unit
   (`def-weil-pbc-standard-smooth-algebra`). Set `d = n - c`.
4. Regard the last `d` variables as coefficients. Regrouping polynomial variables gives
   a square Jacobian presentation (`def-exc-jacobian-presentation`): differentiation in
   the first `c` variables preserves the original Jacobian and its invertible determinant.
5. By `lem-exc-etale-jacobian-presentation` and
   `lem-weil-pbc-etale-ring-map-iff-etale-affine`, the resulting map of spectra is étale.
   The affine-space identification in `def-sbc-affine-space` gives the required map `e`.
6. The composite on rings fixes coefficients and equals the chart's original ring map.
   Spectrum functoriality (`def-weil-affine-spectrum`) and
   `lem-weil-pbc-affine-opens-induced-ring-map-spec-square` identify the composite with
   the restricted original morphism. The chosen opens contain the designated points.
-/
theorem Scheme.Hom.exists_etale_to_affineSpace_of_exists_smooth_appLE
    {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (hx : ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (_ : x ∈ V) (hVU : V ≤ g ⁻¹ᵁ U), (g.appLE U V hVU).hom.Smooth) :
    ∃ (d : ℕ) (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
      (_ : g.base x ∈ U) (_ : x ∈ V) (hVU : V ≤ g ⁻¹ᵁ U)
      (e : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) U.toScheme),
      Etale e ∧
        e ≫ (AffineSpace (ULift.{u} (Fin d)) U.toScheme ↘ U.toScheme) =
          g.resLE U V hVU := by
  obtain ⟨U, hU, V, hV, hxV, hVU, H⟩ := hx
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : Smooth (g.resLE U V hVU) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
    exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso g U V hVU)).mpr H
  obtain ⟨U', hU', V', hV', hxV', hVU', H'⟩ :=
    Smooth.exists_isStandardSmooth (g.resLE U V hVU) ⟨x, hxV⟩
  let := ((g.resLE U V hVU).appLE U' V' hVU').hom.toAlgebra
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := H'
  obtain ⟨d, H''⟩ : ∃ d,
      ((g.resLE U V hVU).appLE U' V' hVU').hom.IsStandardSmoothOfRelativeDimension d :=
    ⟨_, _, _, _, ‹_›, P, rfl⟩
  rw [Scheme.Hom.resLE_appLE] at H''
  have hU'' := hU'.image_of_isOpenImmersion U.ι
  have hV'' := hV'.image_of_isOpenImmersion V.ι
  obtain ⟨e, he, hge⟩ :=
    g.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension hU'' hV'' _ H''
  have hxV'' : x ∈ V.ι ''ᵁ V' := ⟨⟨x, hxV⟩, hxV', rfl⟩
  exact ⟨d, _, _, hU'', hV'', (le_resLE_preimage_iff g hVU U' V').mp hVU' hxV'', hxV'', _, e,
    he, hge⟩

end AlgebraicGeometry
