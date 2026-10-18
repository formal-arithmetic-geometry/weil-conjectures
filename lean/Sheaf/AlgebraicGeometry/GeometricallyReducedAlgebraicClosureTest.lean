/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Geometric reducedness tested on a chosen algebraic closure

Source: Stacks Project, `varieties.tex`, Tags 035X and 020I
(blueprint: lem-trf-geometric-reducedness-algebraic-closure-test).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme over a field is geometrically reduced if and only if its base change to a
chosen algebraic closure is reduced. There are no finiteness or nonemptiness assumptions.

Source: Stacks Project, `varieties.tex`, Tag 035X, (2) iff (6) in positive characteristic;
Tag 020I and faithfully flat descent in characteristic zero
(blueprint: lem-trf-geometric-reducedness-algebraic-closure-test).

Proof plan:
1. Geometric reducedness applies to the particular extension `Ω / k`, so the displayed
   base change is reduced. This also holds for the empty scheme.
2. Conversely, restrict reducedness of this base change to the base changes of the canonical
   affine cover, using `lem-trf-reduced-scheme-open-cover`. Identify each chart with the
   spectrum of its ring tensored with `Ω`, using
   `lem-weil-pbc-fibre-product-affine-spectra`, and apply
   `lem-weil-pbc-affine-scheme-reduced-iff` to obtain reducedness of that tensor product.
3. Use `lem-trf-reducedness-tensor-chosen-algebraic-closure` to replace the chosen closure
   by the canonical algebraic closure, and `lem-trf-affine-geometric-reducedness-criterion`
   to deduce reducedness of each chart ring after every field extension of `k`.
4. For any field extension, its base changes of the original affine charts cover the base
   change of `X`. The tensor-product spectrum description and the affine reducedness
   criterion make every chart reduced. The open-cover criterion then makes the whole base
   change reduced. An empty cover handles the empty scheme. -/
theorem geometricallyReduced_iff_isReduced_pullback_algebraicClosure
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] :
    GeometricallyReduced (X ↘ Spec (.of k)) ↔
      IsReduced (pullback (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) := by
  sorry

end AlgebraicGeometry
