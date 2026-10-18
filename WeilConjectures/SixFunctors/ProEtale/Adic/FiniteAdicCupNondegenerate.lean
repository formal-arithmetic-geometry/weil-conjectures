/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.TraceCupNondegenerate
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicCup

/-!
# Poincaré duality for the cup product on `Hⁿ(S_proét, ℤ/ℓᵐ)`

Let `k` be a separably closed field in which `ℓ` is invertible and `a : S ⟶ Spec k` proper and
smooth of relative dimension `d`. For `i + j = 2d` the cup product pairing
`Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ H^{2d}(S, ℤ/ℓᵐ)` is nondegenerate on both sides
(`AlgebraicGeometry.ProEtale.finiteAdicHCup_nondegenerate`): through the comparison with
`Hom(Λ_S, Λ_S[n])` in `D(S_ét, Λ)`, `Λ = ℤ/ℓᵐ`, the cup product is the étale cup product
(`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH_cupProduct`), whose trace–cup pairing is
nondegenerate for a Tate orientation of `a`
(`AlgebraicGeometry.Etale.TateOrientation.exists_nondegenerate_traceCup`); a Tate orientation exists
by smooth purity (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`,
`sk-thm-smooth-purity`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [IsSepClosed k] {S : Scheme.{u}}
  (a : S ⟶ Spec (.of k)) [IsProper a] {d : ℕ} [SmoothOfRelativeDimension d a]
  [HasCompactification a] [CompactSpace S] [QuasiSeparatedSpace S]

include a in
/-- **The cup product pairing on `Hⁿ(S, ℤ/ℓᵐ)` is nondegenerate in complementary degrees** for `S`
proper and smooth of relative dimension `d` over a separably closed field in which `ℓ` is
invertible. -/
theorem finiteAdicHCup_nondegenerate (hl : (l : k) ≠ 0) (m : ℕ) {i j n : ℕ} (h : i + j = n)
    (hn : n = 2 * d) :
    (∀ x : FiniteAdicH S l m i, (∀ y, finiteAdicHCup l m S h x y = 0) → x = 0) ∧
      (∀ y : FiniteAdicH S l m j, (∀ x, finiteAdicHCup l m S h x y = 0) → y = 0) :=
  sorry

end AlgebraicGeometry.ProEtale
