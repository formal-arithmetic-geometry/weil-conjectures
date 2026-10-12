/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Finite.Stalk

/-! # Extension of pointed étale neighbourhoods from the generic point

Source: Stacks Project, Tags 02GH and 07RP, and blueprint
`lem-sc-affine-generic-second`, proof paragraph 3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A pointed étale neighbourhood over the function field is dominated by a generic
fibre of a pointed étale neighbourhood over the integral scheme.

Source: Stacks Project, Tags 02GH (standard étale presentations) and 07RP;
blueprint `lem-sc-affine-generic-second`, proof paragraph 3.
(blueprint: lem-sc-generic-pointed-etale-extension)

Proof: Restrict the given neighbourhood to an affine standard étale neighbourhood
of the marked point. Choose a nonempty affine open Spec A of D; its fraction field
is K. A standard étale presentation over K uses finitely many coefficients,
including coefficients witnessing invertibility of the derivative. Clear all
denominators and localize A at their nonzero product. The resulting standard
étale algebra over this localization has generic fibre equal to the chosen
standard étale K-algebra. Compose its spectrum with the open immersion into D.
Through the generic-fibre identification, the original geometric marking lifts
to this fibre. Its composite with projection to the extended neighbourhood is a
marking above the given geometric point of D. The canonical identification of
its base-changed marking with the pair of these two markings gives a morphism
in the category of pointed neighbourhoods to the original neighbourhood.
This construction only needs an affine neighbourhood of the marking, so the
original neighbourhood need not be quasi-compact or separated. -/
theorem exists_hom_generic_baseChangeNbhd
    (D : Scheme.{u}) [IsIntegral D]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec D.functionField)
    (d : (pointSmallEtale s).fiber.Elements) :
    ∃ c, Nonempty ((Etale.baseChangeNbhd D.fromSpecFunctionField
      (s ≫ D.fromSpecFunctionField) ⟨s, rfl⟩).obj c ⟶ d) := by sorry

end AlgebraicGeometry.Scheme
