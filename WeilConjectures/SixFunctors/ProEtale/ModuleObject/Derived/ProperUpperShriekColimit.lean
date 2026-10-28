/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarTwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperUpperShriekExistence

/-!
# The proper direct image on `Dᵇc(-)⟦ℚ̄_ℓ⟧` is a left adjoint: fields of infinite cohomological
dimension

Let `ℓ` be a prime, `k` a field in which `ℓ` is invertible and `g : Z ⟶ Y` a proper morphism of
separated `k`-schemes of finite type. By the 2-colimit argument
(`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_forall`,
blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-qlbar`), the case of `k` neither finite nor
separably closed reduces to the case of `𝒪̲_E`
(`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_not`).
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- Blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-qlbar`, for `k` neither finite nor
separably closed: for a proper morphism `g : Z ⟶ Y`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` is a left adjoint. By the 2-colimit argument
(`isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_forall`) this follows from the
case of the finite subextensions `E`
(`isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj_of_not`). -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_not
    (hk : ¬(Finite k ∨ IsSepClosed k)) :
    (boundedConstructibleLowerStar ℓ g).IsLeftAdjoint :=
  have (E : FiniteIntermediateField ℓ) :=
    isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj_of_not ℓ g E hk
  isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_forall ℓ g

end AlgebraicGeometry.ProEtale.CondensedRing
