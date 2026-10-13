/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Local triviality of a descended invertible module

Source: Stacks Project, Tag 0BF2, proof paragraph beginning with shrinking the base;
Tag 0BF0, field rank calculation.
(blueprint: lem-sc-descended-invertible-neighbourhood)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Descent to a vector bundle gives a rank-one trivialization near a base point.
Source: Stacks Project, Tags 0BF2 and 0BF0, rank-one descent and local trivialization.
(blueprint: lem-sc-descended-invertible-neighbourhood)

Proof: Base change f along W.fromSpecResidueField w followed by k. The chosen
structure adjunction unit is an isomorphism from the nonzero structure module on
Spec kappa(w). Hence the fibre cannot be empty: on the empty scheme every module
and its pushforward have zero sections. Choose a fibre point y. Choose a finite
free presentation of N on an open V containing w. Pull this presentation to y
and then to Spec kappa(y). The descent isomorphism identifies this vector space
with the fibre of the invertible M. Its dimension is one over the nonzero field
kappa(y), so the cardinality of the chosen presentation is one. Thus N restricted
to V is the structure module. For any U contained in V, restrict this isomorphism
and pull it back to X times_S U. The cartesian projection square and pullback
composition transport the original descent isomorphism to this base change.
Pullback of the structure module is the structure module, giving the conclusion.
This argument uses just one fibre point, not flatness or properness. A point w
excludes an empty W. No choice of vector bundle data is used in a definition. -/
theorem exists_descendedInvertible_neighbourhood
    {X S : Scheme.{v}} (f : X ⟶ S)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (M : X.Modules) [M.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) (w : W)
    (hM : ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f k)).obj M ≅
        (Modules.tensorPullback (pullback.snd f k)).obj N)) :
    ∃ V : W.Opens, w ∈ V ∧ ∀ U : W.Opens, U ≤ V →
      Nonempty ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf) := by sorry

end AlgebraicGeometry.Scheme
