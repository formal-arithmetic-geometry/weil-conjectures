/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ExternalProductCoefficients
public import WeilConjectures.TraceFormula.OrdinaryKunnethFinite
public import WeilConjectures.TraceFormula.OrdinaryKunnethReduction

/-!
# Vanishing on the boundary for the ordinary Künneth formula, integral coefficients

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`. For morphisms
`i : Z ⟶ X` and `f : U ⟶ Y` of separated `k`-schemes of finite type, a bounded constructible
`𝒪_E`-complex `N` on `X` with `Li^* N = 0` and any `B` on `U`, the complex
`R(𝟙 × f)_* (N ⊠ B)` vanishes on `Z ⨯ Y`
(`ProEtale.CondensedRing.PadicIntegersRingObj.isZero_upperStar_prodMap_lowerStar_prodMap_externalProduct`).

Following the proof of blueprint `lem-trf-ordinary-kunneth` (coefficient transport from finite
coefficients), it is checked after the reduction modulo `ℓ` read on the étale site, which detects
zero objects (`ProEtale.CondensedRing.isZero_of_isZero_etaleReduction`) and commutes with the
pullbacks, the tensor product and the pushforward
(`ProEtale.CondensedRing.etaleReductionUpperStarIso`,
`ProEtale.CondensedRing.nonempty_etaleReductionTensorIso`,
`ProEtale.CondensedRing.etaleReductionLowerStarIso`). This identifies the reduction with the
finite-coefficient complex of `AlgebraicGeometry.Etale.isZero_upperStar_prodMap_lowerStar_prodMap_tensor`
over the finite ring `𝒪_E ⧸ ℓ`, which vanishes by the ordinary Künneth formula with finite
coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {X Y U Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- **Vanishing on the boundary, integral coefficients**: for morphisms `i : Z ⟶ X` and
`f : U ⟶ Y` of separated `k`-schemes of finite type, a bounded constructible `𝒪_E`-complex `N` on
`X` with `Li^* N = 0` and any `B` on `U`, the pullback to `Z ⨯ Y` of `R(𝟙 × f)_* (N ⊠ B)` vanishes.
Its reduction modulo `ℓ`, read on the étale site, is the finite-coefficient complex of
`Etale.isZero_upperStar_prodMap_lowerStar_prodMap_tensor` for the reductions of `N` and `B`
(blueprint `lem-trf-ordinary-kunneth`, coefficient transport). -/
theorem isZero_upperStar_prodMap_lowerStar_prodMap_externalProduct (i : Z ⟶ X) (f : U ⟶ Y)
    {N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
    (hN : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ i).obj N))
    (B : Dᵇc(U.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
      (prod.map i (𝟙 Y))).obj
      ((boundedConstructibleLowerStar ℓ E.1 (prod.map (𝟙 X) f)).obj
        (boundedConstructibleExternalProduct ℓ E.1 N B))) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
