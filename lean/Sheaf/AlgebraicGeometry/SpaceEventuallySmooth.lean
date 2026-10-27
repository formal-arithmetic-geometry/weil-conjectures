/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineDiagramSmoothStage
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Eventual smoothness of a finitely presented algebraic space

Source: Stacks Project, Limits of Spaces, Tag 0CN2 in Situation 084W, specialized
 to affine scheme bases; Morphisms of Spaces, Tag 03ZE, for persistence
(blueprint: lem-sfb-space-eventually-smooth).

The base cone is required to be limiting on underlying schemes. Smoothness of the
presheaf pullback projection uses the existing étale-presentation property; these
pullbacks are the underlying presheaves of the sheaf fibre products. All base schemes
are affine, so their transition maps are automatically affine.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finitely presented algebraic space over an affine stage is smooth at every
sufficiently late stage if its pullback to the inverse limit is smooth.

Source: Stacks Project, Limits of Spaces, Tag 0CN2 in Situation 084W; Morphisms of
Spaces, Tag 03ZE (blueprint: lem-sfb-space-eventually-smooth).

Proof:
1. Quasi-compactness of f₀, tested on the identity of its affine base, makes X₀
   quasi-compact. Choose an affine surjective étale atlas U₀ → X₀ using
   [lem-trf-space-qc-finite-affine-atlas-refinement]. The composite U₀ → Tᵢ₀ is
   locally of finite presentation by [lem-sfb-space-etale-presentation-property-criterion]
   and [lem-sfb-scheme-etale-source-target-properties].
2. Pull this atlas back to every later stage and to the limit. Fibre-product pasting
   identifies Uᵢ with U₀ ×_{Tᵢ₀} Tᵢ. These remain surjective étale scheme atlases by
   [lem-trf-space-fibre-products-etale-covers]. The presentation criterion and scheme
   locality identify limit smoothness with smoothness of U → T.
3. The directed tail i ≥ i₀ has the same limit: extend its cones to an index k by
   choosing a common upper bound of k and i₀; directedness makes this independent
   of the choice and proves uniqueness. Apply [lem-sbc-affine-diagram-smooth-stage]
   to U₀ → Tᵢ₀ and the affine base diagram on this tail, obtaining a smooth stage j.
4. For i ≥ j, pullback pasting identifies Uᵢ → Tᵢ with the base change of Uⱼ → Tⱼ.
   It is smooth by clause (2) of [lem-pc-proper-base-change]. Its surjective étale
   atlas then detects smoothness of Xᵢ → Tᵢ by the presentation criterion and scheme
   locality. Empty sources and non-surjective transitions require no exception. -/
theorem eventually_smooth_of_affine_isLimit
    {S : Scheme.{u}} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (hD : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (i₀ : I)
    (X₀ : AlgebraicSpace S) (f₀ : X₀.obj.obj ⟶ yoneda.obj (D.obj (op i₀)))
    (hlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X₀ (D.obj (op i₀)) f₀)
    (hqc : MapIsQuasiCompact f₀) (hqs : MapIsQuasiCompact (pullback.diagonal f₀))
    (hf : HasEtalePresentationProperty (@Smooth)
      (Limits.pullback.snd f₀ (yoneda.map (c.π.app (op i₀))))) :
    ∃ (j : I) (hj : i₀ ≤ j), ∀ (i : I) (hi : j ≤ i),
      HasEtalePresentationProperty (@Smooth)
        (Limits.pullback.snd f₀ (yoneda.map (D.map (homOfLE (hj.trans hi)).op))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
