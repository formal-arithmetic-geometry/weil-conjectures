/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.WeaklyContractibleSections
public import WeilConjectures.TraceFormula.Specialization.TraitClosedLift
public import WeilConjectures.TraceFormula.Specialization.TraitGenericFibre

/-!

# Higher direct images from the geometric generic point of the trait

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧` the strictly henselian trait,
`i : Spec k' ⟶ S` its closed point and `j : Spec Ω ⟶ S` its geometric generic point. For a
commutative condensed ring `Λ`, the higher direct images `Rⁿ j_* (j^* Λ_S)`, `n > 0`, vanish
after `i^*` (`ProEtale.CondensedRing.isZero_upperStar_traitClosedPoint_obj_rightDerived`).

It suffices to check this on sections over the henselian lifts `W = Spec H_{k'⟦t⟧}(C̄)` of the
w-contractible ind-étale `k'`-algebras `C̄`, which compute the sections of `i^*`
(`ProEtale.CondensedRing.isZero_upperStar_traitClosedPoint_obj_of_forall`). Such a `W` is weakly
contractible, and so is its geometric generic fibre `W ×_S Spec Ω`
(`ProEtale.isWeaklyContractible_pullback_traitGenericPoint_closedLiftSpec`). Sections over a
weakly contractible object are exact, so the sections of `Rⁿ j_* N` over `W` are the cohomology
of the sections over `W ×_S Spec Ω` of an injective resolution of `N`, which vanishes in
positive degrees.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k' : Type u) [Field k'] [IsSepClosed k']

end AlgebraicGeometry.ProEtale.CondensedRing
