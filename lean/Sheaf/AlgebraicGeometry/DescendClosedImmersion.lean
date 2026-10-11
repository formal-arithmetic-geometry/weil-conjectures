/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Descent of closed immersions to a stage of an inverse limit

Source: Stacks Project, Limits, Tag 01ZP, in Situation 081D
(blueprint: lem-weil-pbc-descend-closed-immersion).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finite type morphism between quasi-compact quasi-separated schemes over a
quasi-compact quasi-separated stage becomes a closed immersion at some later stage if its
base change to the limit is a closed immersion.

Source: Stacks Project, Limits, Tag 01ZP, in Situation 081D
(blueprint: lem-weil-pbc-descend-closed-immersion).

Proof:
1. A closed immersion is affine (lem-weil-pbc-closed-immersion-integral-separated-uc).
   Descend affineness to a stage k ≥ i₀ using lem-weil-pbc-descend-affine.
2. Replace i₀ by k. Cartesian square pasting identifies all later base changes with the
   original ones (lem-weil-pbc-cartesian-square-pasting), and local finite type persists
   by lem-weil-pbc-lft-base-change.
3. Cover Y₀ by finitely many affine opens mapping into affine opens of S₀. At stage k
   their preimages and inverse images under fₖ are affine, with finite type ring maps
   (lem-weil-pbc-affine-open-spec-points, lem-weil-pbc-open-fibre-product,
   lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-morphism-into-affine-scheme,
   lem-weil-pbc-lft-affine-pairs).
4. Over each affine base open, the limit is the spectrum of the colimit of the stage
   rings (lem-weil-pbc-limit-affine-transition, lem-weil-pbc-spec-colimit-limit).
5. Identify the affine pieces of every base change with the spectra of the corresponding
   tensor products; the morphism is induced by the base-changed ring map
   (lem-weil-pbc-open-fibre-product, lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-morphism-into-affine-scheme).
6. At the limit these ring maps are surjective by the closed immersion hypothesis
   (lem-weil-pbc-closed-immersion-affine-cover-criterion).
7. Surjectivity descends to a stage on each piece by lem-weil-pbc-colimit-surjective-ring-map
   (Stacks 07RH), and persists under further base change.
8. Directedness gives a common upper bound for the finitely many stages, also above k
   when the cover is empty. The affine cover criterion then makes the morphism at that
   stage a closed immersion (lem-weil-pbc-closed-immersion-affine-cover-criterion). -/
theorem exists_isClosedImmersion_stage_of_locallyOfFiniteType
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left]
    (hf : IsClosedImmersion ((Over.pullback (c.π.app (op i₀))).map f₀).left) :
    ∃ (i : I) (h : i₀ ≤ i),
      IsClosedImmersion
        ((Over.pullback (D.map (homOfLE h).op)).map f₀).left := by
  sorry

end AlgebraicGeometry
