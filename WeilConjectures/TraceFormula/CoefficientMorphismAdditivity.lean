/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.CoefficientMorphismBasic

/-!

# Additivity of the trace formula for Frobenius coefficient morphisms

For an open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under the
Frobenius, and an arbitrary map `ψ : LΦ^* K ⟶ K`, the trace of `RΓ_c(X, ψ) ∘ Φ^♯` is the sum of
the traces of the corresponding operators of the restrictions of `ψ` to `U` and `Z`
(`ProEtale.CondensedRing.trace_compactPullback_comp_eq_add`, blueprint
`prop-trf-trace-additivity-open-closed`, item (3)), and the trace formula in degree one on `U` and
`Z` gives it on `X` (`ProEtale.CondensedRing.TraceFormulaHolds.of_isCompl`, blueprint
`thm-trf-coefficient-morphism-trace-formula`, Step 5).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

/-- **Additivity of the compactly supported Frobenius operator of a coefficient morphism along an
open–closed decomposition** (blueprint `prop-trf-trace-additivity-open-closed`, item (3)): for an
open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under the Frobenius,
and an arbitrary map `ψ : LΦ^* K ⟶ K`, the trace of `RΓ_c(X, ψ) ∘ Φ^♯` on `RΓ_c(X, K)` is the
sum of the traces of the operators `RΓ_c(U, ψ|_U) ∘ Φ_U^♯` and `RΓ_c(Z, ψ|_Z) ∘ Φ_Z^♯` of the
restrictions of `ψ`. -/
theorem trace_compactPullback_comp_eq_add [IsSepClosed k]
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint U)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))] :
    trace ((compactPullback ℓ Φ).app K ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map ψ) =
      trace ((compactPullback ℓ ΦU).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint U)).map
          ((weilUpperStarComparison ℓ ΦU Φ j hj).hom.app K ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map ψ)) +
      trace ((compactPullback ℓ ΦZ).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).map
          ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map ψ)) :=
  sorry

/-- **The trace formula is additive along open–closed decompositions** (blueprint
`thm-trf-coefficient-morphism-trace-formula`, Step 5, from
`prop-trf-trace-additivity-open-closed`, item (3)): for an open immersion `j : U ⟶ X` with closed
complement `i : Z ⟶ X`, both stable under the Frobenius, the trace formula in degree one on `U`
and on `Z` gives it on `X`: the fixed points of `Φ` are those of `Φ_U` and `Φ_Z`, with the same
stalk maps (`ProEtale.CondensedRing.trace_graphStalkMap_upperStar`). -/
theorem TraceFormulaHolds.of_isCompl [IsSepClosed k]
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (hU : TraceFormulaHolds ℓ ΦU)
    (hZ : TraceFormulaHolds ℓ ΦZ) : TraceFormulaHolds ℓ Φ :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
