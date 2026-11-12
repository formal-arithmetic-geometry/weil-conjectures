/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison

/-!
# Local models of integral constructible sheaves

For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a constructible `𝒪_E`-sheaf `C` on a
noetherian scheme `X`, there is a finite stratification of `X` on whose strata `C` is pro-étale
locally of the form `𝒪_{E,S} ⊗_{𝒪_E} P` with `P` a finitely presented (equivalently, finitely
generated: `𝒪_E` is noetherian) `𝒪_E`-module
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_stratification_hasFiniteConstantLocalModel`,
blueprint `lemma-structure-integral-constructible-complexes--2`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- Blueprint `lemma-structure-integral-constructible-complexes--2`: for a constructible
`𝒪_E`-sheaf `C` on a noetherian scheme `X` there is a finite stratification `X = ∐ₐ Xₐ` into
constructible locally closed subschemes on whose strata `C` is pro-étale locally
`𝒪_{E,Xₐ} ⊗_{𝒪_E} P` with `P` finitely generated: `C|_{Xₐ}` has a finite constant local model
(`HasFiniteConstantLocalModel`), i.e. on the members `U` of a pro-étale cover of `Xₐ` it is the
pullback `𝒪_{E,U} ⊗_{𝒪_E} P` of a finitely presented `𝒪_E`-module `P` on the point. -/
theorem exists_stratification_hasFiniteConstantLocalModel {X : Scheme.{u}} [IsNoetherian X]
    {C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)}
    (hC : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) C) :
    ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
      HasFiniteConstantLocalModel (Profinite.padicIntegersRingObj.{u} ℓ E) (S.domain a)
        ((upperStar (Profinite.padicIntegersRingObj.{u} ℓ E) (S.immersion a)).obj C) := by
  have h := ((adicConstructibilityPredicateComparison ℓ X _
    (IsEllAdicCoefficient.integral E)).1 C).1 hC
  rw [IsConstantModelConstructible] at h
  split_ifs at h with hX
  · exact h
  · exact absurd ⟨inferInstance, inferInstance⟩ hX

end AlgebraicGeometry.ProEtale.CondensedRing
