/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Tensor inheritance of the single-complex base-change condition

Source: Stacks Project, perfect.tex, Tag 0DJA, part (1)
(blueprint: lem-pc-rf-single-complex-inherited-tensor-condition).
-/

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Tensoring a map satisfying the single-complex stalkwise base-change condition by an
arbitrary quasi-coherent derived object preserves that condition.  The tensor comparison is
written using a monoidal structure on the derived pullback (one exists, Stacks 079U) and its
inverse tensorator.
Source: Stacks Project, perfect.tex, Tag 0DJA, part (1).  Proof: at a stalk, apply the
transitivity of derived tensor products to the stalk of `E` and the assumed comparison for
`K`; the stalk ring of the fibre product is a localization, hence flat, so cohomology commutes
with the final scalar extension.  This is exactly the local computation in the node proof,
using `lem-pc-derived-tensor-transitivity`.
(blueprint: lem-pc-rf-single-complex-inherited-tensor-condition). -/
theorem singleComplexInheritedTensorCondition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S)
    (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : schemeDerivedQCohCategory X) (K' : schemeDerivedQCohCategory X')
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K.obj K'.obj φ) :
    Nonempty (Functor.Monoidal (derivedPullback g')) ∧
    ∀ [Functor.Monoidal (derivedPullback g')] (E : schemeDerivedQCohCategory X),
      SingleComplexBaseChange.StalkCondition f f' g g' sq
        (E.obj ⊗ K.obj) (((derivedPullback g').obj E.obj) ⊗ K'.obj)
        ((Functor.Monoidal.μIso (derivedPullback g') E.obj K.obj).inv ≫
          ((derivedPullback g').obj E.obj ◁ φ)) := by
  sorry

end AlgebraicGeometry
