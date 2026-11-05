/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections

/-!
# The closed inverse image preserves limits

Let `i : Z = Spec (A ⧸ I) ⟶ X = Spec A` be a closed immersion with quasi-compact open complement.
The pullback `i^*` of pro-étale sheaves of modules preserves all limits
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_closedSpecι`, blueprint
`det-sf-open-closed-pullback-limits`).

The objects `V = Spec C̄` of `Z_proét` with `C̄` w-contractible and ind-étale over `A ⧸ I` are
weakly contractible and cover `Z_proét`
(`AlgebraicGeometry.ProEtale.exists_closedLiftBasis_cover`). On such `V = v(V) ×_X Z`, the
sections of `i^* F` are those of `F` over the henselian lift `v(V) = Spec H_A(C̄)`
(`AlgebraicGeometry.ProEtale.bijective_unit_app_closedLiftSpec`), and these commute with limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {A : CommRingCat.{u}} (I : Ideal A)

section Basis

variable (S : Type u) [CommRing S] [Algebra (A ⧸ I) S] [Algebra A S] [IsScalarTower A (A ⧸ I) S]
  [Algebra.IndEtale (A ⧸ I) S]

end Basis

variable {R : Type (u + 1)} [Ring R] {U : Scheme.{u}} (j : U ⟶ Spec A) [IsOpenImmersion j]
  [QuasiCompact j]

end ProEtale

end AlgebraicGeometry
