/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ExternalProductExtendScalars
public import WeilConjectures.TraceFormula.PointComplement

/-!

# Integral models with vanishing stalk at a point

Let `K` be a bounded constructible `ℚ̄_ℓ`-complex on `X` whose stalk at a rational point `x`
vanishes. Then `K` has an integral model `M` over some `𝒪_E` whose stalk at `x` vanishes as well
(`ProEtale.CondensedRing.exists_integralModel_isZero_upperStar`): take any integral model `K₀`
(`ProEtale.exists_padicAlgCl_iso_integralModel`) and replace it by its extension by zero
`j_! j^* K₀` from the complement of `x`; since `K_x = 0`, `K = j_! j^* K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Integral models with vanishing stalk**: a bounded constructible `ℚ̄_ℓ`-complex `K` with
`K_x = 0` at a rational point `x` has an integral model `M` over some `𝒪_E`, `ℚ̄_ℓ ⊗ M ≅ K`,
with `M_x = 0`. -/
theorem exists_integralModel_isZero_upperStar (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (x : RationalPoint X)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :
    ∃ (E : FiniteIntermediateField ℓ) (M : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧),
      Nonempty ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj M ≅ K) ∧
        IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ x).obj
          M) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
