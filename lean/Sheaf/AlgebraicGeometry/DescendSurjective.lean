/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Sheaf.AlgebraicGeometry.LimitContainedInConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Surjectivity descends to a finite stage of an inverse limit

Source: Stacks Project, Limits, Lemma 07RR in Situation 081D
(blueprint: lem-weil-pbc-descend-surjective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finitely presented morphism between quasi-compact, quasi-separated schemes
at a stage of an inverse system with affine transitions is surjective at some later stage
if its base change to the limit is surjective.

Source: Stacks Project, Limits, Lemma 07RR in Situation 081D
(blueprint: lem-weil-pbc-descend-surjective).

Proof:
1. Quasi-compactness of X₀ and quasi-separatedness of Y₀ make f₀ quasi-compact
   (lem-weil-pbc-qcqs-morphism-permanence). Chevalley's theorem gives the constructible
   image E = f₀(X₀) (lem-weil-pbc-chevalley-constructible-image,
   def-weil-constructible-subset).
2. For each base T → S₀, the map X₀ × T → Y₀ × T is also the base change of f₀ along
   Y₀ × T → Y₀, by pasting the two cartesian squares
   (def-pc-fibre-product, lem-weil-pbc-cartesian-square-pasting).
3. The image of this map is the inverse image of E under Y₀ × T → Y₀
   (lem-weil-pbc-base-change-image).
4. Surjectivity over S therefore implies that Y → Y₀ maps into E
   (def-weil-surjective-morphism).
5. The schemes Yᵢ over the upper tail i ≥ i₀ have limit Y and affine transitions
   (lem-weil-pbc-scheme-over-limit, def-weil-pbc-category-colimit). They are quasi-compact
   and quasi-separated by affine permanence and composition with Y₀
   (lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-qcqs-morphism-permanence).
6. Apply lem-weil-pbc-limit-contained-in-constructible to E to obtain a stage i ≥ i₀
   whose projection Yᵢ → Y₀ maps into E.
7. Step 3 now says that the image of fᵢ is all of Yᵢ, which is the required surjectivity
   (def-weil-surjective-morphism). -/
theorem exists_surjective_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (_hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (_hf : Surjective (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      Surjective (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
  sorry

end AlgebraicGeometry
