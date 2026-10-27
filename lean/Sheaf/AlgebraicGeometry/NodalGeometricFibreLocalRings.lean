/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # Local rings and projection used in nodal geometric-fibre conditions

Source: Stacks Project, curves.tex, Tags 0C5A (definition-nodal-family) and 0CBY
(lemma-etale-local-structure-nodal-family)
(blueprint: def-sfb-nodal-geometric-fibre-local-rings).

These are the maximal-ideal completion of a scheme stalk, the split-node ring
`Ω[[u,v]]/(uv)`, and the canonical second projection of a geometric fibre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.NodalFiber

/-- The completion of the actual stalk at its maximal ideal.
Source: Stacks Project, curves.tex, Tags 0C5A and 0CBY
(blueprint: def-sfb-nodal-geometric-fibre-local-rings). -/
noncomputable def completedLocalRing {F : Scheme.{u}} (z : F) : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (F.presheaf.stalk z)) (F.presheaf.stalk z)

/-- The componentwise commutative-ring structure on the maximal-ideal completion.
Source: Stacks Project, curves.tex, Tags 0C5A and 0CBY
(blueprint: def-sfb-nodal-geometric-fibre-local-rings). -/
noncomputable instance instCommRingCompletedLocalRing {F : Scheme.{u}} (z : F) :
    CommRing (completedLocalRing z) :=
  inferInstanceAs
    (CommRing (AdicCompletion (IsLocalRing.maximalIdeal (F.presheaf.stalk z))
      (F.presheaf.stalk z)))

/-- The split-node ring `Ω[[u,v]]/(uv)`, with variables indexed by `Fin 2`.
Source: Stacks Project, curves.tex, Tags 0C5A and 0CBY
(blueprint: def-sfb-nodal-geometric-fibre-local-rings). -/
noncomputable def powerSeriesQuotient (Ω : Type u) [CommRing Ω] : Type u :=
  MvPowerSeries (Fin 2) Ω ⧸
    Ideal.span ({MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1} :
      Set (MvPowerSeries (Fin 2) Ω))

/-- The quotient commutative-ring structure on the split-node ring.
Source: Stacks Project, curves.tex, Tags 0C5A and 0CBY
(blueprint: def-sfb-nodal-geometric-fibre-local-rings). -/
noncomputable instance instCommRingPowerSeriesQuotient (Ω : Type u) [CommRing Ω] :
    CommRing (powerSeriesQuotient Ω) :=
  Ideal.Quotient.commRing _

/-- The canonical projection of the fibre to its coefficient-field spectrum.
An algebraically closed coefficient field gives the geometric-fibre projection.
Source: Stacks Project, curves.tex, Tags 0C5A and 0CBY
(blueprint: def-sfb-nodal-geometric-fibre-local-rings). -/
noncomputable def projection {X S : Scheme.{u}}
    (f : X ⟶ S) (Ω : Type u) [Field Ω] (g : Spec (.of Ω) ⟶ S) :
    pullback (C := Scheme) f g ⟶ Spec (.of Ω) :=
  pullback.snd f g

end AlgebraicGeometry.NodalFiber
