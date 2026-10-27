/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.TraceFormula.NodalOpenLocus

/-! # Nonempty nodal fibres of proper curve families

Source: Stacks Project, moduli-curves.tex, Tag 0DSY; curves.tex, definition-nodal
(blueprint: def-sfb-curve-moduli-groupoids).

The ambient families and cartesian arrows are those of `ProperCurveModuli`.
This module supplies only their nonempty nodal geometric-fibre predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperCurveFamily

/-- Nonempty pure one-dimensional nodal geometric fibres of the existing proper
curve family. Purity and ordinary nodes are checked on every étale scheme chart;
empty charts are allowed, while the whole geometric fibre must be nonempty.
No connectedness, genus or characteristic restriction is imposed.
Source: Stacks Project, moduli-curves.tex, Tag 0DSY; curves.tex, definition-nodal
(blueprint: def-sfb-curve-moduli-groupoids). -/
def HasNonemptyNodalGeometricFibres {S : Scheme.{u}} {T : Over S}
    (X : ProperCurveFamily T) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T.left),
    Nonempty (AlgebraicSpace.Point (Limits.pullback X.projection
      (yoneda.map (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)))) ∧
      ∀ (U : Over S) (b : yoneda.obj U ⟶ Limits.pullback X.projection
        (yoneda.map (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T))),
        AlgebraicSpace.IsEtale b → U.left.IsPureDimension 1 ∧
          ∀ x : U.left,
            (∃ W : U.left.Opens, x ∈ W ∧ AlgebraicGeometry.Smooth
              (W.ι ≫ (yoneda.preimage (b ≫ Limits.pullback.snd X.projection
                (yoneda.map (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)))).left)) ∨
              IsOrdinaryNode Ω U.left x

end AlgebraicGeometry.ProperCurveFamily
