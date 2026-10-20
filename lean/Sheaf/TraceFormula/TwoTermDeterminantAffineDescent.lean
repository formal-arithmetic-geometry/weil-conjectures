/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.TraceFormula.AffineTwoTermDeterminantData

/-! # Descent of affine determinant functors

Source: Stacks Project, Perfect Complexes, Tags 0FJX and 0FJY.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
variable [d : ∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- A determinant system on affine schemes extends to every scheme by descent.
Source: Stacks Project, Perfect Complexes, Tags 0FJX and 0FJY; Descent, Tag 023T
(blueprint: lem-trf-two-term-determinant-affine-descent).

Proof: cover X by affine opens, refining until the chosen object has two-term finite
locally free models with constant ranks. Apply the given affine functor on each open.
For affine subopens of an overlap, the cartesian comparisons and the derived restriction
isomorphisms give transition isomorphisms. Naturality, the pullback composition law and
κ's associativity make these agree under further restriction and satisfy the cocycle
law. Equal maps of sheaves are detected on affine bases, so these are transitions on
whole overlaps, even when overlaps are not affine. Open covers are fpqc: they are flat,
and each affine open has a finite principal refinement. Use the explicit sheaf-gluing
construction in fpqc descent to obtain the determinant module. It is invertible locally,
hence globally. Full faithfulness glues the maps of the affine functors and proves the
functor laws. The same full faithfulness glues model comparisons and the normalized
zero and evaluation maps, and makes them independent of cover and refinement.
For g:Y→X, cover Y by affine V mapping into affine model opens U of X. Pulling a finite
locally free model back gives a two-term model for Lg*L by the flat-complex comparison.
The affine cartesian maps on V agree on affine refinements of overlaps, so glue to the
asserted comparison. Its naturality, identity law and composition law follow by
restriction to these affine covers and the corresponding equations in the given
system. κ's unit and associativity laws identify all iterated derived restrictions.
No quasi-compactness or separatedness of X or Y is used. On the empty scheme use the
empty gluing diagram, whose unique module is simultaneously zero and the unit. -/
theorem descend_affineTwoTermDeterminantData
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (κ : TwoTermDeterminantPullbackCoherence.{u, w})
    (A : AffineTwoTermDeterminantData κ) :
    Nonempty (TwoTermDeterminantFunctorData κ) := by
  sorry

end AlgebraicGeometry
