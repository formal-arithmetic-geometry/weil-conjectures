/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization

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
  sorry

end AlgebraicGeometry.Scheme
