/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension

/-!
# Fibre dimension after base change

Source: Stacks Project, Tag 02FY (lemma-dimension-fibre-after-base-change), part (1)
(blueprint: lem-sc-fibre-dimension-after-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Source: Stacks Project, Tag 02FY (lemma-dimension-fibre-after-base-change), part (1)
(blueprint: lem-sc-fibre-dimension-after-base-change).
The fibre `(X')_{s'}` is identified with `X_s ×_{κ(s)} κ(s')` by an isomorphism
compatible with the maps to `X_s` and to `Spec κ(s')` (the base change of `X_s` along
`κ(s) → κ(s')`); `f x = s` is the cartesian-square relation `s = g(s') = f(x)`.
Proof: `Spec κ(s') → S' → S` factors through `Spec κ(s) → S` via the residue-field map,
so pullback pasting gives the fibre identification. `X_s` is locally of finite type over
`κ(s)` by base change; the dimension at a point is local, so on an affine neighbourhood
the field-extension dimension lemma (Tag 00P4) gives `dim_{x'} (X')_{s'} = dim_x X_s`.
-/
theorem fibre_dimension_after_base_change {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S)
    (x' : ↥(Limits.pullback f g)) :
    let f' : Limits.pullback f g ⟶ S' := Limits.pullback.snd f g
    let x : X := Limits.pullback.fst f g x'
    let s' : S' := f' x'
    let s : S := g s'
    (∃ e : f'.fiber s' ≅
        Limits.pullback (f.fiberToSpecResidueField s) (Spec.map (g.residueFieldMap s')),
      e.hom ≫ Limits.pullback.fst _ _ ≫ f.fiberι s =
          f'.fiberι s' ≫ Limits.pullback.fst f g ∧
        e.hom ≫ Limits.pullback.snd _ _ = f'.fiberToSpecResidueField s') ∧
      f x = s ∧
      topologicalKrullDimAt (f'.asFiber x') = topologicalKrullDimAt (f.asFiber x) := by
  sorry

end AlgebraicGeometry
