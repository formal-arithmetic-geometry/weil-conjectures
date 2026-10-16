/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying

import all Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemComparison

/-! # Quotients of formal systems remain adic

Source: Stacks Project, Tag 088A, the systems F_n/K^e F_n.
(blueprint: lem-weil-pbc-formal-second-ideal-quotient-adic).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem quotientProjection_map {X : Scheme.{u}} (J : X.IdealSheafData)
    {F G : X.Modules} (f : F ⟶ G) (n : ℕ) :
    formalModuleQuotientπ J n F ≫ formalModuleQuotientMap J f (Nat.le_refl n) =
      f ≫ formalModuleQuotientπ J n G := by
  simp only [formalModuleQuotientπ, formalModuleQuotientMap, cokernel.π_desc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Termwise K-quotients of an I-adic coherent system are I-adic.
Source: Stacks Project, Tag 088A, construction of G_e.
(blueprint: lem-weil-pbc-formal-second-ideal-quotient-adic).

Proof: Each term is a coherent quotient by the coherent completion construction.
The I-power product of the quotient is zero: precomposing its multiplication with
the epimorphic K-quotient projection reduces this to the original I-annihilation.
Interchange the I and K quotients using the canonical double-quotient comparison,
then apply the K-quotient functor to the original I-adic transition isomorphism.
The projection identity of the comparison and the original transition identity,
after cancellation of the K-quotient projection, identify the resulting map with
the actual transition. -/
theorem formalSecondIdealQuotient_coherent
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) (e : ℕ) :
    IsCoherentFormalModule I ((M.obj ⋙ formalCompletionFunctor K).flip.obj (op e)) := by
  sorry

end AlgebraicGeometry
