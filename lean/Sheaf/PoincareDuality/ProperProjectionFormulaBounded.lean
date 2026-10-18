/-
Copyright (c) 2026 Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import Sheaf.Paper.ProperBaseChangeRational

/-! Proper direct-image input to the exceptional projection formula. -/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

universe u

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

attribute [local instance 3000] projectionDerivedMonoidal
attribute [local instance 4000] projectionModuleAbelian projectionModuleMonoidal
  projectionModuleHasDerived
attribute [local instance 5000] projectionSheafMonoidal projectionCoefficientMonObj
  projectionModuleCategory

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (ℓ : ℕ) [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

include ℓ k in
/-- Proper projection on bounded constructible complexes of condensed module objects.

Source: the proper projection clause of `det-thm-sfb-proper-base-change-rational`,
transported by `lem-pd-module-ringed-topos-derived-comparison`, as in Step 2 of
`nt-target-poincare-isiso`.

Here the first complex is the actual extension by zero along the open part of a
compactification. It is bounded constructible by the existing open lower-shriek theorem.

Proof: identify the actual module-object pullback adjunction and its oplax tensor map
with the ringed-topos versions. At finite coefficients, proper base change identifies
the projection map on each geometric stalk with the cohomological projection formula
on the proper geometric fibre. Resolve the second factor by finite free complexes;
the formula holds for the coefficient unit and is preserved by shifts, cones and the
colimits computing the resolution. Passage to the derived complete integral models
is detected modulo every positive power of the uniformizer. Rationalization preserves
these isomorphisms, and filtered scalar extension gives the algebraic closure case.
The integral and unit-ball presentations are identified with the same valuation-ring
coefficient object. The coefficient alternatives in `IsEllAdicFinitenessCoefficient`
give these integral, rational and algebraic-closure cases.
The comparison respects the counit and tensor structure, so the resulting isomorphism
is the specified adjoint of the counit tensored with the identity.

(blueprint: lem-pd-condensed-proper-projection-formula)
-/
theorem isIso_properProjection_bounded (f : X ⟶ Y) (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦Λ⟧) (B : Dᵇc(Y.left)⟦Λ⟧) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ c.g).projectionMorphism
      ((D((c.i)_!open⟦Λ⟧)).obj K.obj) B.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
