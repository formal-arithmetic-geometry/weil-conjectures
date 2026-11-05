/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientRingBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.DisjointUnion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftConnectedComponents
public import WeilConjectures.RingTheory.ProEtale.SpanIdempotents
public import WeilConjectures.TraceFormula.Specialization.TraitClosedLift
public import WeilConjectures.TraceFormula.Specialization.TraitGenericFibre

/-!

# The unit of the geometric generic point of the trait

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧` the strictly henselian trait,
`i : Spec k' ⟶ S` its closed point and `j : Spec Ω ⟶ S` its geometric generic point. For a
commutative condensed ring `Λ`, the unit `Λ_S ⟶ j_* j^* Λ_S` becomes an isomorphism after `i^*`
(`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_unit_app`).

It suffices to check this on sections over the henselian lifts `W = Spec H_{k'⟦t⟧}(C̄)` of the
w-contractible ind-étale `k'`-algebras `C̄`, which compute the sections of `i^*`
(`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_of_forall`).

Here `W = Spec H` and `W ×_S Spec Ω = Spec (H ⊗ Ω)` are spectra of w-contractible rings
(`ProEtale.isWContractibleRing_closedLift_tensorProduct_traitGenericField`), so the sections of
`Λ_S` over `W` and of `Λ_Ω` over `W ×_S Spec Ω` are `Λ(π₀ W)` and `Λ(π₀(W ×_S Spec Ω))`, and on
sections the unit is the map induced by `π₀(W ×_S Spec Ω) ⟶ π₀(W)`
(`ProEtale.bijective_unitCompUpperStarCompInv_app`). This is a homeomorphism, every idempotent of
`H ⊗ Ω` coming from `H`
(`ProEtale.bijective_pullback_fst_comp_closedLiftSpec_traitGenericPoint`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {k' : Type u} [Field k'] [IsSepClosed k']

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable (k' : Type u) [Field k'] [IsSepClosed k']

end AlgebraicGeometry.ProEtale.CondensedRing
