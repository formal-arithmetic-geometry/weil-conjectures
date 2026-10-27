/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.DensePoints
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Density of images of smooth pointed curves

Source: Milne, Abelian Varieties, Chapter I, Lemmas 3.5(b) and 3.6, printed p.18,
and the proof of Theorem 3.4, printed p.19
(blueprint: lem-sfb-smooth-pointed-curves-dense).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Images of smooth geometrically integral curves through a prescribed rational point are
jointly dense. The curve maps are allowed to be constant, including when the target has
dimension zero. Each structure morphism `g i` is a curve in the sense of `IsCurve`, which
includes separatedness and finite type; its dimension is required to be exactly one.

Source: Milne, Abelian Varieties, Chapter I, Lemmas 3.5(b) and 3.6, printed p.18,
and the proof of Theorem 3.4, printed p.19
(blueprint: lem-sfb-smooth-pointed-curves-dense).

Proof:
1. Induct strongly on the finite dimension of the target, supplied by
   `lem-sfb-point-tangent-cone-dimension`. In dimension zero, finite type over a field
   gives Noetherianity (`lem-weil-pbc-finite-type-over-noetherian`), and
   `lem-sc-zero-dim-noetherian-finite-discrete` gives a finite discrete underlying space.
   Integrality makes it a singleton. Use the constant map from the affine line through
   its origin; `sbc-lem-affine-space-smooth` gives smoothness, and the polynomial
   presentation gives separatedness, finite type, dimension one and geometric integrality.
   In dimension one, use the target itself and its identity map.
2. In dimension at least two, `lem-sfb-smooth-prescribed-tangent-hypersurface` supplies
   smooth geometrically integral hypersurfaces through the point with every prescribed
   tangent hyperplane. Apply induction on each hypersurface and compose its curve maps
   with the inclusion into the target. Any closed subset containing all eligible curve
   images then contains each of these hypersurfaces.
3. Give that closed subset its reduced closed subscheme structure. By
   `lem-sfb-point-tangent-cone-dimension`, its tangent cone contains every tangent
   hyperplane, hence every vector. The field is infinite, so a polynomial vanishing
   on all these vectors is zero. The cone is therefore the whole tangent affine space,
   whose dimension is the target dimension by `lem-sf-noetherian-polynomial-dimension`.
   The strict dimension inequality for a proper closed subset in the tangent-cone lemma
   rules out a proper closed subset containing all the curve images.
4. Eligible images form a subset of the power set of the target. Their union is dense
   by the preceding step. For each nonempty open subset choose an eligible curve map
   whose image meets it, and index the chosen maps by these nonempty opens. The union
   of their images meets every nonempty open and is dense. This index is a set in the
   universe of the target's underlying space. Apply the construction to `X` and `x₀`.
-/
theorem exists_smooth_pointed_curves_dense
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [IsSeparated f]
    [GeometricallyIntegral f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x₀ : f.fieldPoints k) :
    ∃ (I : Type u) (C : I → Scheme.{u})
      (g : ∀ i : I, C i ⟶ Spec (.of k))
      (c : ∀ i : I, (g i).fieldPoints k) (ι : ∀ i : I, C i ⟶ X),
      (∀ i : I, IsCurve (g i) ∧ Smooth (g i) ∧ GeometricallyIntegral (g i) ∧
        topologicalKrullDim (C i) = 1 ∧ ι i ≫ f = g i ∧ (c i).1 ≫ ι i = x₀.1) ∧
      Dense (⋃ i : I, Set.range (ι i)) := by
  sorry

end AlgebraicGeometry
