/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Sheaf.AlgebraicGeometry.ProperBirationalCurveFinite

/-!
# Proper birational maps to normal integral curves

Source: Stacks Project, Varieties, Tags 0AB7 and 0BFP, and Morphisms, Tag 0AB1
(blueprint: lem-trf-proper-birational-normal-curve-iso).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A proper dominant birational map of integral curves onto a normal curve is an isomorphism.
Source: Stacks Project, Varieties, Tags 0AB7 and 0BFP; Morphisms, Tag 0AB1
(blueprint: lem-trf-proper-birational-normal-curve-iso).

The birational hypothesis is bijectivity of the actual stalk map at the generic point of `E`.
Dominance sends that point to the generic point of `C`, so its source is canonically `k(C)`
and its target is `E.functionField = k(E)`.

Proof: apply `lem-trf-proper-birational-curve-finite` (Tag 0AB7). The target is Noetherian
and one-dimensional, and the generic field extension is an isomorphism, hence finite.
The codimension-one finiteness criterion applies at every target point. Finiteness is local
on the target, so `p` is finite. Then apply `lem-trf-finite-birational-normal-iso` (Tag 0AB1):
on affine opens, the finite inclusion of domains has the same fraction field, and the
normal target ring is integrally closed in that field. Thus the rings coincide and `p` is
an isomorphism. Neither step needs normality of `E` or perfection of `k`. -/
theorem isIso_of_isProper_birational_normal_curve
    {k : Type u} [Field k] {C E : Scheme.{u}}
    [C.Over (Spec (.of k))] [E.Over (Spec (.of k))]
    [IsIntegralCurve (C ↘ Spec (.of k))] [IsIntegralCurve (E ↘ Spec (.of k))]
    (p : E ⟶ C) [p.IsOver (Spec (.of k))] [IsProper p] [IsDominant p]
    (hbirational : Function.Bijective (p.stalkMap (genericPoint E) :
      C.presheaf.stalk (p (genericPoint E)) ⟶ E.functionField))
    (hnormal : ∀ x : C, IsDomain (C.presheaf.stalk x) ∧
      IsIntegrallyClosed (C.presheaf.stalk x)) : IsIso p := by
  sorry

end AlgebraicGeometry
