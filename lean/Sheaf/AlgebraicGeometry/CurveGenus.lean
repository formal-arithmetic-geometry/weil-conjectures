/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.GenusInvariant

/-!
# Curves and genus

Source: blueprint, `sec-abelian-varieties/sk-def-curve/_section.md`, order 528
(blueprint: sk-def-curve).

The definitions of curves, connected curves and genus are the existing `IsCurve`,
`IsConnectedCurve` and `Scheme.Hom.genus` in `WeilConjectures.AlgebraicGeometry.Curve`.
Smoothness and properness mean `Smooth` and `IsProper` of the structure morphism.
Only the final genus-invariance parenthetical needs a statement here.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The genus of a smooth proper connected curve is invariant under extension of
algebraically closed fields.

Source: blueprint, `sec-abelian-varieties/sk-def-curve/_section.md`, final parenthetical
(blueprint: sk-def-curve).

Proof: apply `genus_jacobian_invariant` (lem-sc-genus-invariant) to the curve and
extension. Eliminate the three existential witnesses and retain the first conjunct,
the equality of genera. The genera are the differential-form genera of `Scheme.Hom.genus`
(def-sc-genus); the Jacobian clauses are not needed. -/
theorem Scheme.Hom.genus_baseChange_of_isAlgClosed
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] :
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).genus = f.genus := by
  sorry

end AlgebraicGeometry
