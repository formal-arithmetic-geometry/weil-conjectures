/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.Algebra.Central.ReducedNorm
import WeilConjectures.FieldTheory.Cr
import WeilConjectures.FieldTheory.Tsen

/-!
# Brauer vanishing over algebraic extensions of curve function fields

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/
lem-sc-function-field-cd-one.md, Proof, third paragraph
(blueprint: lem-sc-brauer-algebraic-function-field-zero).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The second etale cohomology of `G_m` vanishes over any finite separable extension `E`
of an algebraic extension `L` of the function field of an integral connected curve over an
algebraically closed field.

Source: blueprint sec-curve-estimates/sk-prop-h2/lem-sc-function-field-cd-one.md,
Proof, third paragraph (blueprint: lem-sc-brauer-algebraic-function-field-zero).

Proof: `E` is algebraic over the function field since `L` is algebraic and `E/L` is finite.
For a homogeneous form of degree `d` in `N > d` variables over `E`, its finitely many
coefficients lie in a finite extension `K'` of the function field. By `lem-sc-tsen` the
function field is C1, and by `lem-sc-c1-finite-extension` so is `K'`. The form has a
nontrivial zero over `K'`, hence over `E`. Thus `E` is C1, and `lem-sc-c1-brauer-trivial`
gives the vanishing of its Brauer group, equivalently its second etale cohomology of `G_m`.
-/
theorem IsConnectedCurve.isZero_etaleCohomology_gm_algebraic_extension
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsConnectedCurve (C ↘ Spec (.of k))] [IsIntegral C]
    (L : Type v) [Field L] [Algebra C.functionField L]
    [Algebra.IsAlgebraic C.functionField L]
    (E : Type w) [Field E] [Algebra L E] [FiniteDimensional L E]
    [Algebra.IsSeparable L E] :
    IsZero ((Etale.cohomology AddCommGrpCat.{w + 1} (Spec (.of E)) 2).obj
      ((DerivedCategory.singleFunctor
        (Sheaf (Spec (.of E)).smallEtaleTopology AddCommGrpCat.{w + 1}) 0).obj
          (Spec (.of E)).gmSheaf)) := by
  sorry

end AlgebraicGeometry
