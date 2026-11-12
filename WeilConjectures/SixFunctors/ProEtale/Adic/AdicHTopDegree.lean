/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.ZModSelfInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.NumberTheory.Padics.RankOneCriterion
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite

/-!
# Top-degree pro-étale cohomology with coefficients `ℤ/ℓᵐ` and `ℤ_ℓ`

Let `k` be an algebraically closed field in which the prime `ℓ` is invertible and
`a : X ⟶ Spec k` proper, smooth of relative dimension `d` and geometrically connected. Then
`H^{2d}(X_proét, ℤ/ℓᵐ)` has exactly `ℓᵐ` elements, and `H^{2d}(X_proét, ℤ_ℓ) ≅ ℤ_ℓ`.

Through the comparison `Hom(Λ_X, Λ_X[n]) ≅ Hⁿ(X_proét, ℤ/ℓᵐ)` in `D(X_ét, Λ)`, `Λ = ℤ/ℓᵐ`
(`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`), the first statement is the trace
isomorphism `H^{2d}(X, Λ) ≅ Λ(-d)` (`AlgebraicGeometry.Etale.TateOrientation.
bijective_untwistedTraceMap_comp_cohomologyAddEquivCompactSupport`) for a Tate orientation given
by smooth purity (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), combined
with the triviality of Tate twists over `k`
(`AlgebraicGeometry.Etale.nonempty_tateObject_iso_unit`) and `End(Λ_k) = Λ`
(`AlgebraicGeometry.Etale.bijective_smul_id_unit`). The second follows by the Bockstein and
Milnor sequences, since `H^{2d+1}(X_proét, ℤ_ℓ) = 0`.

## Main statements

- `AlgebraicGeometry.ProEtale.nat_card_finiteAdicH_two_mul`: `#H^{2d}(X_proét, ℤ/ℓᵐ) = ℓᵐ`.
- `AlgebraicGeometry.ProEtale.nonempty_linearEquiv_integralAdicH_two_mul`:
  `H^{2d}(X_proét, ℤ_ℓ) ≅ ℤ_ℓ` as `ℤ_ℓ`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- **Top-degree cohomology has `ℓᵐ` elements.** For `a : X ⟶ Spec k` proper, smooth of
relative dimension `d` and geometrically connected over an algebraically closed field `k` in which
`ℓ` is invertible, `H^{2d}(X_proét, ℤ/ℓᵐ)` has cardinality `ℓᵐ`. -/
theorem nat_card_finiteAdicH_two_mul {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (d : ℕ) [IsProper a] [SmoothOfRelativeDimension d a]
    [GeometricallyConnected a] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ) :
    Nat.card (FiniteAdicH X l m (2 * d)) = l ^ m := by
  let Λ := ULift.{u + 1} (ZMod (l ^ m))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated a
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (ringChar Λ) := by
    rw [ringChar.eq Λ (l ^ m)]
    infer_instance
  have : HasInvertibleExponent Λ (Spec (.of k)) :=
    ⟨l ^ m, Nat.pos_of_ne_zero (NeZero.ne _), ULift.ext (by simp [Λ]), by
      simpa using ((Ne.isUnit (pow_ne_zero m hl)).map (Scheme.ΓSpecIso (.of k)).inv.hom)⟩
  have : HasInvertibleExponent Λ X := .of_hom a
  obtain ⟨θ⟩ := Etale.nonempty_iso_dualizingComplex_twistShift Λ (d := d) a (𝟙 _)
  obtain ⟨e⟩ := Etale.nonempty_tateObject_iso_unit Λ k (-d)
  let φ := Etale.TateOrientation.bijective_untwistedTraceMap_comp_cohomologyAddEquivCompactSupport
    a θ.symm
  rw [← Nat.card_congr (unitShiftAddEquivFiniteAdicH l m X (2 * d)).toEquiv, Nat.cast_mul,
    Nat.cast_ofNat, Nat.card_congr (Equiv.ofBijective _ φ),
    Nat.card_congr (Iso.homCongr (Iso.refl (𝟙_ _)) e),
    ← Nat.card_congr (Equiv.ofBijective _ (Etale.bijective_smul_id_unit Λ (Spec (.of k))))]
  simp [Λ]

/-- **Top-degree `ℓ`-adic cohomology.** For `a : X ⟶ Spec k` proper, smooth of relative
dimension `d` and geometrically connected over an algebraically closed field `k` in which `ℓ` is
invertible, `H^{2d}(X_proét, ℤ_ℓ) ≅ ℤ_ℓ` as `ℤ_ℓ`-modules.

`M = H^{2d}(X_proét, ℤ_ℓ)` is a finitely generated `ℤ_ℓ`-module
(`AlgebraicGeometry.ProEtale.module_finite_integralAdicH`). As `H^{2d+1}(X_proét, ℤ_ℓ) = 0`, the
Bockstein sequence identifies `M / ℓᵐ M` with `H^{2d}(X_proét, ℤ/ℓᵐ)`, which has `ℓᵐ` elements
(`AlgebraicGeometry.ProEtale.nat_card_finiteAdicH_two_mul`); this forces `M ≅ ℤ_ℓ`
(`PadicInt.nonempty_linearEquiv_of_nat_card`). -/
theorem nonempty_linearEquiv_integralAdicH_two_mul {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (d : ℕ) [IsProper a] [SmoothOfRelativeDimension d a]
    [GeometricallyConnected a] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) :
    Nonempty (IntegralAdicH X l (2 * d) ≃ₗ[ℤ_[l]] ℤ_[l]) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated a
  have hfin (m n : ℕ) : Finite (FiniteAdicH X l m n) := finite_finiteAdicH l a hl m n
  have := hfin 1 (2 * d)
  have : Module.Finite ℤ_[l] (IntegralAdicH X l (2 * d)) :=
    module_finite_integralAdicH X l (2 * d) fun m n _ ↦ hfin m n
  have hvan : Subsingleton (IntegralAdicH X l (2 * d + 1)) :=
    subsingleton_H_continuousSheaf_of_profinite a d
      (topologicalKrullDim_le_of_smoothOfRelativeDimension a d) (PadicInt.powOpenAddSubgroup l)
      (PadicInt.powOpenAddSubgroup_succ_le l) (PadicInt.eq_zero_of_forall_mem_powOpenAddSubgroup l)
      _ (by lia)
  refine PadicInt.nonempty_linearEquiv_of_nat_card l (fun m ↦ reduction X l m (2 * d))
    (fun m y ↦ ?_) (fun m _ h ↦ exists_eq_pow_smul_of_reduction_eq_zero X l m (2 * d) h)
    (fun m _ ↦ nat_card_finiteAdicH_two_mul a d l hl m)
  simpa using pow_smul_mem_range_reduction X l m (2 * d) 0
    (fun x _ ↦ by simp [Subsingleton.elim x 0]) y

end AlgebraicGeometry.ProEtale
