/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion
import Sheaf.AlgebraicGeometry.FieldBasePointFibreIsomorphism
import WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescent

/-!
# Smoothness at a point of a flat family under base change

Source: Stacks Project, Morphisms, Tag 02V4, case (1),
`lemma-set-points-where-fibres-smooth`
(blueprint: lem-sfb-scheme-flat-smooth-point-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Smoothness near a point of a flat locally finitely presented scheme family is
equivalent to smoothness near any point above it after an arbitrary base change.
There is no flatness requirement on the base-change morphism.

Source: Stacks Project, Morphisms, Tag 02V4, case (1),
`lemma-set-points-where-fibres-smooth`
(blueprint: lem-sfb-scheme-flat-smooth-point-base-change).

Proof:
1. Flatness and local finite presentation pass from `f` to `pullback.snd f h`
   by lem-weil-pbc-flat-morphism-base-change and clause (3) of
   lem-weil-pbc-qcqs-morphism-permanence. In particular both stalk maps are flat
   (def-weil-flat-morphism), so the pointwise fibre criterion applies to both.
2. For ascent, pull back a smooth open neighbourhood of `pullback.fst f h x`.
   It is an open neighbourhood of `x` by lem-weil-pbc-open-fibre-product.
   Local finite presentation is preserved by base change. For formal smoothness,
   compose a lifting problem with the projection to the original neighbourhood,
   lift there, and pair the lift with the given map to the new base. The fibre
   product universal property gives the desired lift, compatible with restriction
   (def-sbc-smooth-morphisms and def-pc-fibre-product).
3. For reflection, lem-trf-smooth-at-point-fibre-criterion makes the fibre of
   `pullback.snd f h` smooth near its point over `x`. By def-pc-scheme-fibre and
   lem-weil-pbc-fibre-of-base-change this is the extension of the original fibre
   by the residue-field extension at the image of `x`; the projection sends its
   marked point to the original fibre point over `pullback.fst f h x`.
4. Choose a finitely presented affine chart `Spec A` of that original fibre near
   this point (def-sbc-locally-finite-presentation and
   lem-weil-pbc-qcqs-morphism-permanence). Its pullback is an open neighbourhood
   (lem-weil-pbc-open-fibre-product), identified with `Spec (K ⊗[k] A)` by
   lem-weil-pbc-fibre-product-affine-spectra. Its point corresponds to a prime
   whose contraction under `a ↦ 1 ⊗ a` is the original point. Restrict the smooth
   neighbourhood to this chart; open restrictions preserve smoothness by the
   lifting definition (def-sbc-smooth-morphisms).
5. Translate this smoothness to ring smoothness at that prime using
   lem-trf-smooth-fibre-affine-ring-at-prime and
   lem-weil-pbc-field-base-point-fibre-isomorphism: a scheme over a field is its
   sole residue fibre, and `(K ⊗[k] A) ⊗[K] K` identifies with `K ⊗[k] A`.
   Apply lem-weil-pbc-smooth-at-prime-field-extension-descent to the finite type
   algebra `A` to descend smoothness to the contracted prime.
6. By lem-trf-affine-smooth-prime-scheme-neighbourhood this gives a smooth open
   neighbourhood in the original fibre. Apply
   lem-trf-smooth-at-point-fibre-criterion to `f`, using its flatness from step 1,
   to get smoothness near `pullback.fst f h x`. This proves reflection and the
   equivalence. An empty pullback has no points to check. -/
theorem smooth_at_point_pullback_snd_iff_of_flat
    {U T T' : Scheme.{u}} (f : U ⟶ T) [Flat f] [LocallyOfFinitePresentation f]
    (h : T' ⟶ T) (x : pullback (C := Scheme.{u}) f h) :
    (∃ V : (pullback f h).Opens, x ∈ V ∧ Smooth (V.ι ≫ pullback.snd f h)) ↔
      ∃ W : U.Opens, pullback.fst f h x ∈ W ∧ Smooth (W.ι ≫ f) := by
  sorry

end AlgebraicGeometry
