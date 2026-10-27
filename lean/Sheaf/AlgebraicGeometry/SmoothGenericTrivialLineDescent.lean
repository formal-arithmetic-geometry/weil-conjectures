/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-! # Descent of a generically fibre-trivial invertible module

Source: Stacks Project, Divisors, Tag 0BD7, specialized to the smooth regular setting
of the vertical-divisor consequence used in Milne, Algebraic Groups, Theorem 18.32,
printed pp.395--396 (blueprint: lem-sfb-smooth-generic-trivial-line-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An invertible module trivial on the generic fibre of a smooth family with
geometrically integral fibres is a tensor pullback from the regular integral base.
Source: Stacks Project, Divisors, Tag 0BD7, and the vertical-divisor consequence in
Milne, Algebraic Groups, Theorem 18.32, printed pp.395--396
(blueprint: lem-sfb-smooth-generic-trivial-line-descent).

Proof:
1. The regularity predicates give local Noetherianity of S and Y. Apply clause (1)
   of rem-pc-regular-normal to S to obtain normality of its local rings. Together
   with integrality these are the base hypotheses of Stacks Tag 0BD7.
2. By lem-pc-smooth-flat, f is flat and locally of finite presentation. The affine
   presentations in def-sbc-locally-finite-presentation are finite type, so
   lem-weil-pbc-lft-pointwise-criterion gives local finite type. Geometric integrality
   applied to the identity extension of every residue field gives integral nonempty
   fibres. These verify the remaining morphism hypotheses of Tag 0BD7.
3. By lem-sc-integral-function-field-affine-fraction the generic stalk is the fraction
   field of every nonempty affine coordinate ring. Thus the displayed tensor pullback
   is the restriction to the generic fibre in lem-sfb-normal-noetherian-generic-line-pullback.
   Apply that lemma to M and its given trivialization to obtain N and f* N ≅ M. -/
theorem smoothGenericTrivialLineDescent
    (k : Type u) [Field k] (S Y : Scheme.{u})
    [S.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (hS : IsRegularScheme S) (hY : IsRegularScheme Y)
    [IsIntegral S] [IsIntegral Y]
    [IsSeparated (S ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (f : Y ⟶ S) [Smooth f] [Surjective f] [GeometricallyIntegral f]
    (M : Y.Modules) [M.IsInvertible]
    (hM : Nonempty ((Scheme.Modules.tensorPullback
      (pullback.fst f (S.fromSpecStalk (genericPoint S)))).obj M ≅
        SheafOfModules.unit (pullback f (S.fromSpecStalk (genericPoint S))).ringCatSheaf)) :
    ∃ N : S.Modules, N.IsInvertible ∧
      Nonempty ((Scheme.Modules.tensorPullback f).obj N ≅ M) := by
  sorry

end AlgebraicGeometry
