/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyDualityFrobenius

/-!
# Finiteness of `Hⁿ(S_proét, ℤ/ℓᵐ)` over a separably closed field

Let `k` be a separably closed field in which `ℓ` is invertible and `S` a separated `k`-scheme of
finite type. The cohomology groups `Hⁿ(S, ℤ/ℓᵐ)` are finite
(`AlgebraicGeometry.ProEtale.finite_finiteAdicH`): through the comparison
`Hⁿ(S_proét, ℤ/ℓᵐ) ≅ Hom_{D(S_ét, Λ)}(Λ_S, Λ_S[n])`, `Λ = ℤ/ℓᵐ`
(`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`), they are the cohomology groups of
`RΓ(S, Λ)`, a perfect complex of `Λ`-modules
(`AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections`, blueprint `sk-lem-finite`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [IsSepClosed k] {S : Scheme.{u}}
  (a : S ⟶ Spec (.of k)) [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]
  [CompactSpace S] [QuasiSeparatedSpace S]

include a in
/-- The classes `Λ_S ⟶ Λ_S[n]` of `D(S_ét, Λ)`, `Λ = ℤ/ℓᵐ`, form a finite group, for `S`
separated of finite type over a separably closed field in which `ℓ` is invertible. -/
theorem finite_unitShift (hl : (l : k) ≠ 0) (m : ℕ) (n : ℤ) :
    Finite (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦n⟧) :=
  sorry

include a in
/-- **Finiteness of `Hⁿ(S, ℤ/ℓᵐ)`**, for `S` separated of finite type over a separably closed
field in which `ℓ` is invertible. -/
theorem finite_finiteAdicH (hl : (l : k) ≠ 0) (m n : ℕ) : Finite (FiniteAdicH S l m n) :=
  have := finite_unitShift l a hl m n
  Finite.of_equiv _ (unitShiftAddEquivFiniteAdicH l m S n).toEquiv

end AlgebraicGeometry.ProEtale
