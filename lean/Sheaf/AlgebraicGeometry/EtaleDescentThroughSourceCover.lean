/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension

/-!
# Etaleness descends through a surjective etale source cover

Source: Stacks Project, Descent, Tag 036W, `lemma-etale-etale-local-source`,
applied to a singleton etale covering (blueprint: lem-trf-etale-descent-through-source-cover).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If `p : Y ⟶ X` is surjective and etale and `p ≫ h` is etale, then `h` is etale.
There are no separation, finite-type, Noetherian or quasi-compactness assumptions.
Source: Stacks Project, Descent, Tag 036W, `lemma-etale-etale-local-source`;
Morphisms, Tag 02K6 (blueprint: lem-trf-etale-descent-through-source-cover).

Proof:
1. By def-weil-etale-morphism, `p` is flat and locally of finite presentation. By
   lem-weil-pbc-etale-smooth-zero-dimensional-fibres, `p ≫ h` is smooth. Apply
   lem-sbc-smooth-flat-surjective-source-descent to obtain smoothness of `h`, hence
   local finite presentation by def-sbc-smooth-morphisms. No quasi-compactness is needed.
2. Both `p` and `h` are locally of finite type: for each affine target open, use
   lem-weil-pbc-affine-opens-basis to cover its inverse image by affine opens. By
   lem-weil-pbc-lfp-affine-opens-finite-presentation the associated algebras have finite
   presentations; their finitely many polynomial generators generate them as algebras.
   This is def-weil-finite-type-morphism; the open cover need not be finite.
3. Given `x : X`, choose `y : Y` with `p y = x` using def-weil-surjective-morphism.
   By lem-weil-pbc-etale-smooth-zero-dimensional-fibres for `p` and `p ≫ h`, the dimensions
   at `y` of their fibres over `x` and `h x` are zero. Flatness of `p` at `y` and
   lem-sbc-flat-composite-fibre-dimension-at-point give
   `0 = dim_y Y_(h x) = dim_y Y_x + dim_x X_(h x) = 0 + dim_x X_(h x)`.
   Thus the fibre of `h` at `x` has dimension zero at the corresponding point.
4. Apply lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension at each `x`, using
   smoothness from step 1 and fibre dimension zero from step 3. These etale open
   neighbourhoods cover `X`; lem-weil-pbc-etale-local-on-source gives etaleness of `h`.
   For empty `X` use the empty open covering. If `Y` is empty, surjectivity forces `X`
   empty too. All inputs concern arbitrary schemes. -/
theorem Etale.of_comp_of_surjective_etale {T X Y : Scheme.{u}}
    (h : X ⟶ T) (p : Y ⟶ X) [Surjective p] [Etale p] [Etale (p ≫ h)] : Etale h := by
  have : Smooth h := Smooth.of_comp_of_flat_of_surjective p h
  have hdim (x : X) : topologicalKrullDimAt (h.asFiber x) = 0 := by
    obtain ⟨y, rfl⟩ := p.surjective x
    have hp := (smooth_and_fibre_dimension_zero_of_etale p).2.1 y
    have hcomp := (smooth_and_fibre_dimension_zero_of_etale (p ≫ h)).2.1 y
    have hd := flat_composite_fibre_dimension_at_point p h y (Flat.stalkMap p y)
    rw [hcomp, hp, zero_add] at hd
    exact hd.symm
  have hlocal (x : X) : ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ h) := by
    obtain ⟨U, -, hx, hU⟩ := exists_etale_open_of_smooth_of_fibre_dimension_zero
      h x ⊤ (by trivial) (by infer_instance) (hdim x)
    exact ⟨U, hx, hU⟩
  choose U hx hU using hlocal
  exact IsZariskiLocalAtSource.of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩) hU

end AlgebraicGeometry
