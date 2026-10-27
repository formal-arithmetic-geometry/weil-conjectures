/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Eventual properness of a finitely presented algebraic space

Source: Stacks Project, Spaces and Morphisms of Spaces, Situation 084W and Tag 08K1;
Morphisms of Spaces, Tag 04WP (blueprint: lem-sfb-space-eventually-proper).

The base schemes are over Spec Z. All base changes use the existing sheaf fibre product
and its projection, and properness is tested after arbitrary algebraic-space base change.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finitely presented algebraic space over a stage of an inverse system of affine
schemes is proper at every sufficiently late stage if its limit base change is proper.
The initial stage need not be a least index; no transition is assumed surjective.
Source: Stacks Project, Situation 084W, Tag 08K1 and Tag 04WP
(blueprint: lem-sfb-space-eventually-proper).

Proof:
1. Properness implies separatedness. By lem-sfb-space-descend-separated, choose i₁ ≥ i₀
   so every later map is separated. Finite presentation persists by
   lem-sfb-space-flat-proper-fp-locality and implies finite type on affine etale charts.
   The upper tail has the same limit: extend a cone by choosing common upper bounds;
   passing to a further upper bound proves independence and uniqueness.
2. Apply lem-sfb-space-weak-chow over the affine base at i₁. It gives a proper universally
   surjective map X'₁ → X₁ from a quasi-compact separated scheme, and an immersion
   X'₁ → Pⁿ over that base. Base change this diagram to each stage and to the limit.
   The universal property identifies its iterated fibre products with these base changes
   (lem-trf-space-fibre-products-etale-covers). Projective spaces commute with base change
   by def-nagata-projective-space-base-change. Immersions persist by
   lem-weil-pbc-immersion-base-change-lft.
3. At the limit the composite X' → X → T is proper by lem-sfb-space-proper-base-change
   and lem-sfb-space-proper-composition. Restricting to scheme tests gives scheme
   properness. The projection Pⁿ_T → T is proper and separated by
   lemma-nagata-projective-space-base-change-proper. Thus X' → Pⁿ_T is proper by
   lem-weil-pbc-proper-over-separated, and closed by lem-weil-pbc-proper-immersion-closed.
4. Descend that closed immersion by lem-weil-pbc-descend-closed-immersion. The Chow source
   is quasi-compact and separated, hence qcqs; projective space is proper over an affine
   base, hence qcqs by lem-weil-pbc-qcqs-morphism-permanence. The immersion is locally of
   finite type by lem-weil-pbc-immersion-base-change-lft. At some i₂ ≥ i₁ the immersion is
   closed; its composite with the projective projection is proper by
   lem-weil-pbc-proper-fp-permanence.
5. The map at i₂ is separated and finitely presented by step 1, hence finite type. For
   any scheme W over its base and closed subset C of the base-changed space, universal
   surjectivity of the Chow map gives f_W(C) = p_W(π_W⁻¹(C)). The inverse image is closed
   by continuity; p_W is a proper scheme morphism by lem-weil-pbc-proper-fp-permanence,
   so its image is closed. No flatness is required of W.
6. For an arbitrary algebraic-space base change W and etale scheme chart V → W, the
   inverse image of f_W(C) is the image under f_V of the inverse image of C. Indeed,
   matching point classes have field-valued representatives agreeing over a common field
   extension by lem-trf-space-fibre-products-etale-covers, and give a point of the fibre
   product. Step 5 makes this image closed. The final topology of
   def-a1-space-point-topology therefore makes f_W(C) closed. Individual charts need not
   be surjective. This proves universal closedness, and hence properness at i₂.
7. Every j ≥ i₂ is a base change of this proper stage: pullback associativity identifies
   its source with X₀ ×_{T₀} T_j. Apply lem-sfb-space-proper-base-change (Tag 04WP).
   Taking i = i₂ proves the conclusion, including j = i. -/
theorem eventually_proper_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))
    [∀ i : I, IsAffine (D.obj (op i)).left]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f₀ : X₀ ⟶ schemeSpace (D.obj (op i₀)))
    (hfp : MapIsLocallyOfFinitePresentation f₀ ∧ MapIsQuasiCompact f₀.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f₀.hom.hom))
    (hf : MapIsProper (enlargedFibreProductFst
      (ObjectProperty.homMk ⟨yoneda.map (c.π.app (op i₀))⟩ :
        schemeSpace c.pt ⟶ schemeSpace (D.obj (op i₀))) f₀)) :
    ∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hj : i ≤ j),
      MapIsProper (enlargedFibreProductFst
        (ObjectProperty.homMk ⟨yoneda.map (D.map (homOfLE (le_trans hi hj)).op)⟩ :
          schemeSpace (D.obj (op j)) ⟶ schemeSpace (D.obj (op i₀))) f₀) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
