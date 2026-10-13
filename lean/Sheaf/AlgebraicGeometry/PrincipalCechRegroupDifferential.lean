/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalCechTotalRegrouping
import Sheaf.AlgebraicGeometry.PrincipalCechColumns
import Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal
import Sheaf.CategoryTheory.DoubleComplexTotal

/-! # Differential compatibility of the explicit regrouping

Source: Stacks, Tag 08D1, signs of alternating total cochains
(blueprint: lem-sc-principal-cech-regroup-differential).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

/-- The explicit graded regrouping commutes with the total differential.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-regroup-differential).

Proof: precompose the equation with every diagonal coproduct inclusion and read
its subset coordinates. The vertical part of Mathlib's total differential has
sign p.negOnePow. A nonzero coordinate has card(J)=p+1 and therefore p≥0;
this sign acts as (-1 : A)^(card(J)-1). The chain-map equation of e p identifies
the vertical differential with the section differential in this coordinate.
For the horizontal part, the displayed hypothesis identifies the column map
with principalCechHorizontal. Its subset projection is the sum over j in J of
(-1) raised to the number of earlier indices times restriction from J.erase j.
The source row has card(J.erase j)=p+1, and its vertical degree equals the
coefficient degree of the target; principalCech_erase_degree gives precisely
the transport in principalCechDifferentialValue. Empty erased sets contribute
zero on both sides. These are exactly the two terms of that formula, which
principalCechDifferential_exists identifies with the chosen differential.
Coproduct inclusions and product projections detect equality. For an empty
cover there are no subset coordinates; outside the supported rows the sources
are zero. This argument imposes no bound on the vertical degrees. -/
theorem principalCechTotalRegroup_comm
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (B : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (e : ∀ p, B.X p ≅ (principalCechColumnFunctor r f p).obj F)
    (he : ∀ p, B.d p (p + 1) ≫ (e (p + 1)).hom =
      (e p).hom ≫ (principalCechHorizontal r f p).app F) (n : ℤ) :
    principalCechTotalRegroup r f F B e n ≫ principalCechDifferential r f F n =
      (B.total (ComplexShape.up ℤ)).d n (n + 1) ≫
        principalCechTotalRegroup r f F B e (n + 1) := by sorry

end
end AlgebraicGeometry
