/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.CupProduct
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantHPullback
public import WeilConjectures.Algebra.Module.AdicDualityTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicFrobenius

/-!
# Frobenius-compatible duality for `Hⁱ(S, ℚ̄_ℓ)` from finite-level étale dualities

Let `S` be a connected quasi-compact quasi-separated scheme and `e : S ≅ S` an automorphism (the
geometric Galois Frobenius of `X̄ = X ×_{k₀} k̄`). The explicit comparison
`Hom_{D(S_ét, Λ)}(Λ_S, Λ_S[n]) ≅ Hⁿ(S_proét, ℤ/ℓᵐ)`, `Λ = ℤ/ℓᵐ`
(`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`), intertwines the Frobenius operator
`x ↦ ε⁻¹ ≫ Le^* x ≫ ε[n]` of the canonical Weil datum `ε : Le^* Λ_S ≅ Λ_S` with the pullback `e^*`
of pro-étale cohomology
(`AlgebraicGeometry.ProEtale.finiteAdicHPullback_unitShiftAddEquivFiniteAdicH`).

Consequently, nondegenerate finite-level pairings on `Hom(Λ_S, Λ_S[i]) × Hom(Λ_S, Λ_S[j])` which
are similitudes for the étale Frobenius operators give the finite-level Frobenius similitudes
`hQF` of `AlgebraicGeometry.ProEtale.exists_isPerfPair_adicConstantH`, for the pullbacks `e^*` on
the integral cohomology `Hⁿ(S, ℤ_ℓ)`; hence a perfect pairing on `Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ)`
which is a similitude for any endomorphisms extending `e^*`
(`AlgebraicGeometry.ProEtale.exists_isPerfPair_adicConstantH_of_unitPairing`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (m : ℕ) (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]

/-- **Finite-level pro-étale cohomology is étale `Ext`, explicitly.** On a quasi-compact
quasi-separated scheme `S`, `Hom_{D(S_ét, Λ)}(Λ_S, Λ_S[n]) ≅ Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)`,
`Λ = ℤ/ℓᵐ`. -/
noncomputable def unitShiftAddEquivFiniteAdicH (n : ℕ) :
    (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(n : ℤ)⟧) ≃+
      FiniteAdicH S l m n :=
  (Etale.unitShiftAddEquivExt _ S n).trans (extAddEquivFiniteAdicH l m S n)

/-- **The comparison `Hom(Λ_S, Λ_S[n]) ≅ Hⁿ(S_proét, ℤ/ℓᵐ)` is Frobenius equivariant.** For an
automorphism `e` of a connected quasi-compact quasi-separated scheme `S`, it intertwines the
Frobenius operator of the canonical Weil datum `ε : Le^* Λ_S ≅ Λ_S` with the pullback `e^*` of
pro-étale cohomology. -/
theorem finiteAdicHPullback_unitShiftAddEquivFiniteAdicH [ConnectedSpace S] (e : S ≅ S) (n : ℕ)
    (x : 𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(n : ℤ)⟧) :
    finiteAdicHPullback e l m n (unitShiftAddEquivFiniteAdicH l m S n x) =
      unitShiftAddEquivFiniteAdicH l m S n (Etale.frobeniusOperator e.hom
        (Etale.shiftWeilDatum e.hom (Etale.leftDerivedUpperStarUnitIso _ e.hom).hom n) x) := by
  rw [unitShiftAddEquivFiniteAdicH, AddEquiv.trans_apply, AddEquiv.trans_apply,
    finiteAdicHPullback_extAddEquivFiniteAdicH]
  congr 1
  exact (Etale.unitShiftAddEquivExt_leftDerivedUpperStar _ e.hom n x).symm

end AlgebraicGeometry.ProEtale
