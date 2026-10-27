/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Eventual flatness of a finitely presented algebraic space

Source: Stacks Project, Limits of Spaces, Tag 08K0, last assertion, in Situation 084W;
Morphisms of Spaces, Tag 03MO (blueprint: lem-sfb-space-eventually-flat).

The base system consists of affine schemes over the terminal scheme Spec Z. Finite
presentation includes quasi-compactness and quasi-compactness of the relative diagonal.
All base changes use the existing first projection of the actual sheaf fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finitely presented algebraic space over a stage of an affine inverse system that
is flat over the limit is flat over every sufficiently late stage.
Source: Stacks Project, spaces-limits.tex, Tag 08K0, last assertion in Situation 084W;
spaces-morphisms.tex, Tag 03MO (blueprint: lem-sfb-space-eventually-flat).

Proof:
1. The affine base T₀ is quasi-compact by lem-weil-pbc-affine-scheme-qcqs. Since f₀
   is quasi-compact, X₀ is quasi-compact and has a quasi-compact surjective etale
   scheme atlas C → X₀, using lem-sfb-space-flat-proper-fp-locality. Apply
   lem-a1-qc-map-affine-etale-neighbourhood to get an affine scheme U₀ and an etale
   map U₀ → X₀ whose pullback to C is surjective. Lifting field-valued points first
   to C and then to that pullback proves U₀ → X₀ surjective, by
   lem-trf-space-fibre-products-etale-covers.
2. Put Uᵢ = U₀ ×_{T₀} Tᵢ and U = U₀ ×_{T₀} T. The natural pairs of projections
   identify these with the pullbacks of U₀ → X₀ to Xᵢ and X. Hence their maps to
   Xᵢ and X remain surjective etale by lem-trf-space-fibre-products-etale-covers.
   The limit T is affine by lem-weil-pbc-limit-affine-transition. All Uᵢ and U are
   affine by lem-weil-pbc-fibre-product-affine-spectra.
3. The composite U₀ → T₀ is locally of finite presentation, and U → T is flat, by
   chart testing in lem-sfb-space-flat-proper-fp-locality applied to f₀ and f.
4. Apply lem-weil-pbc-descend-flat-finite-presentation to U₀ → T₀ over the affine
   base system. All initial schemes are qcqs by lem-weil-pbc-affine-scheme-qcqs;
   transition maps are affine because they are maps between affine schemes. This
   gives i ≥ i₀ with Uᵢ → Tᵢ flat.
5. Chart testing gives Xᵢ → Tᵢ flat. For every j ≥ i, the universal property of
   fibre products identifies Xⱼ → Tⱼ with its base change along Tⱼ → Tᵢ. Flatness
   persists by lem-sfb-space-flat-proper-fp-locality. Empty source spaces are included:
   the same empty atlases and chart tests apply. -/
theorem eventually_flat_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))
    (c : Cone D) (hc : IsLimit c)
    [∀ i : I, IsAffine (D.obj (op i)).left] (i₀ : I)
    (X₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f₀ : X₀ ⟶ schemeSpace (D.obj (op i₀)))
    (hfp : MapIsLocallyOfFinitePresentation f₀ ∧ MapIsQuasiCompact f₀.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f₀.hom.hom))
    (hflat : MapIsFlat (enlargedFibreProductFst
      (ObjectProperty.homMk ⟨yoneda.map (c.π.app (op i₀))⟩ :
        schemeSpace c.pt ⟶ schemeSpace (D.obj (op i₀))) f₀)) :
    ∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hij : i ≤ j),
      MapIsFlat (enlargedFibreProductFst
        (ObjectProperty.homMk ⟨yoneda.map (D.map (homOfLE (le_trans hi hij)).op)⟩ :
          schemeSpace (D.obj (op j)) ⟶ schemeSpace (D.obj (op i₀))) f₀) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
