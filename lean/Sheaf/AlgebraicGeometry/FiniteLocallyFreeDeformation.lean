/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Thickening
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteThickeningCartesian
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-!
# Finite locally free degree under flat first-order deformation

Source: Stacks Project, More on Morphisms, Tag 06AG, lemma-deform-property, part (23),
with the target equal to the base; fixed degree follows from the identical residue-field
fibres (blueprint: lem-sfb-finite-locally-free-deformation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A flat morphism whose reduction along a first-order thickening is finite locally free
of degree `d` is itself finite locally free of degree `d`.
Source: Stacks Project, Tag 06AG, part (23), with `Y' = S'` and `Y = S₀`.
(blueprint: lem-sfb-finite-locally-free-deformation)

Proof:
1. The reduction is finite and locally of finite presentation by
   `def-pc-finite-locally-free`. The first-order thickening is a finite-order thickening
   with exponent two (`def-sbc-first-order-thickening`). Apply
   `lem-weil-pbc-thickening-finite-cartesian`, transporting across pullback symmetry,
   to obtain finiteness of `q'`. Its flatness is assumed.
2. For each affine open `U' = Spec A` in `S'`, its reduction is `Spec (A/I)` by
   `lem-weil-pbc-closed-immersion-affine-cover-criterion`, and `I² = 0`.
   The morphism `W' = V' ×[S'] U' → U'` is flat by
   `lem-weil-pbc-flat-morphism-base-change`. The universal property
   `def-pc-fibre-product` identifies its reduction with `V₀ ×[S₀] U₀`.
   On affine opens the reduced coordinate maps are finitely presented by
   `lem-weil-pbc-lfp-affine-opens-finite-presentation`. Thus the reduction is locally
   of finite presentation (`def-sbc-locally-finite-presentation`). Apply
   `lem-sfb-flat-deformation-lfp` with exponent two to obtain this property for `W'`.
3. Each point of `V'` lies over an affine open of `S'`, so these local presentations
   give local finite presentation of `q'`. Together with finiteness and flatness this
   is finite local freeness (`def-pc-finite-locally-free`).
4. The thickening is a homeomorphism, so each `s'` comes from a unique `s₀`.
   Their residue fields are canonically isomorphic by
   `lem-weil-pbc-closed-immersion-residue-field-iso`. The pullback universal property
   identifies the two scheme-theoretic fibres over these fields, respecting structure
   maps. Hence their global-section algebras have the same vector-space dimension.
   The reduced fibre has dimension `d`, so every fibre of `q'` has degree `d`.
   This includes degree zero, and the fibre assertion is vacuous for an empty base. -/
theorem Scheme.Hom.isFiniteLocallyFreeOfDegree_of_firstOrderThickening
    {S₀ S' V' : Scheme.{u}} (i : S₀ ⟶ S') (q' : V' ⟶ S')
    (hi : IsFirstOrderThickening i) [Flat q'] (d : ℕ)
    (h₀ : (pullback.fst i q').IsFiniteLocallyFreeOfDegree d) :
    q'.IsFiniteLocallyFreeOfDegree d := by
  sorry

end AlgebraicGeometry
