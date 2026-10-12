/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Sheaf.AlgebraicGeometry.DescendAffine
import Sheaf.RingTheory.FiniteMapColimitDescent

/-!
# Finiteness descends to a finite stage of a limit

Source: Stacks Project, Limits, Lemma 01ZO (lemma-descend-finite-finite-presentation),
under Situation 081D (blueprint: lem-weil-pbc-descend-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Finiteness of a base change to an inverse limit descends to a finite stage.

Source: Stacks Project, Limits, Lemma 01ZO, in Situation 081D
(blueprint: lem-weil-pbc-descend-finite).

Proof:
1. A finite morphism is affine, so `lem-weil-pbc-descend-affine` gives a stage where
   the base-changed morphism is affine.
2. Replace the initial index by that stage; cartesian-square pasting identifies all
   later base changes with base changes of this affine morphism, and local finite type
   is stable under base change.
3. Choose a finite affine cover of the quasi-compact target, with each member mapping
   into an affine open of the initial base. Affine transitions and the affine morphism
   make its inverse images at the chosen stage affine. Local finite type gives finite
   type coordinate ring maps (`lem-weil-pbc-lft-affine-pairs`).
4. The affine opens over the limit have coordinate rings given by filtered colimits
   of the corresponding stage rings.
5. Open fibre products and the affine-spectrum fibre-product lemma identify the pieces
   of every base change with spectra of the corresponding tensor products, and their
   morphisms with spectra of the tensor-product ring maps.
6. On the limit pieces, finiteness of the morphism gives finite coordinate ring maps;
   transport module generators across the ring isomorphisms of step 5.
7. Apply `lem-weil-pbc-colimit-finite-ring-map` to each finite type map to obtain a stage
   where it is finite. Images of its module generators still generate at larger stages.
8. Directedness gives one stage working for all members of the finite cover (choose
   the initial stage if the cover is empty). The criterion
   `lem-weil-pbc-finite-local-on-target` proves the resulting morphism finite.
-/
theorem exists_isFinite_baseChange_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    (hfinite : IsFinite (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsFinite (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
  sorry

end AlgebraicGeometry
