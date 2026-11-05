/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.TraceFormula.Specialization.PointsSupport

/-!

# Complexes supported at finitely many closed points

Let `V` be a separated scheme of finite type over a separably closed field `k` and `S` a finite
set of closed points of `V`. A bounded constructible `ℚ̄_ℓ`-complex `C` on `V` whose restriction to
`V ∖ S` vanishes, and whose global sections `RΓ(V, C)` vanish, is zero
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`, blueprint
`det-nearby-kunneth-finite-support`).

The closed points need not be rational: `k` need not be perfect. This generalises
`WeilConjectures.TraceFormula.Specialization.PointsSupport` (rational points). The residue field
`κ(z)` of a closed point is finite, hence purely inseparable, over `k`, so it is separably closed
(`ProEtale.CondensedRing.isSepClosed_of_locallyOfFiniteType`). Every bounded constructible complex
on `Spec κ(z)` is then a finite direct sum of shifts of the unit, and `RΓ(Spec κ(z), -)` detects
vanishing (`ProEtale.CondensedRing.isZero_of_isZero_lowerStar_toPoint_of_isSepClosed`): a summand
`𝟙⟦d⟧ = La^* 𝟙⟦d⟧ ⟶ E` is adjoint to a morphism into `Ra_* E = 0`. The open–closed triangle at a
closed point then splits as for rational points, and one concludes by induction on `S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Residue fields of closed points -/

section ResidueField

variable {k : Type u} [Field k] (K : Type u) [Field K]

end ResidueField

/-! ### Closed points as schemes over `k` -/

section ClosedPoint

variable {k : Type u} [Field k] {V : Over (Spec (.of k))}

end ClosedPoint

/-! ### Global sections on a separably closed point -/

section Point

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

end Point

/-! ### Open–closed vanishing at a closed point -/

section Vanishing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

end Vanishing

/-! ### Finitely many closed points -/

section Points

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

end Points

end AlgebraicGeometry.ProEtale.CondensedRing
