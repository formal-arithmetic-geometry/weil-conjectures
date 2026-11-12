/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionTower

/-!
# The inverse image of integral constructible complexes is already complete

Let `g : W ⟶ X` be a morphism of schemes with `W` noetherian, and `K ∈ Dᵇc(X, 𝒪_E)`. The
completed inverse image of `K` (Stacks, Tag 09BP; Bhatt–Scholze, §6.5) is the derived
`ℓ`-adic completion of the ordinary inverse image `Lg^* K`, that is, the homotopy limit
`R lim_n (Lg^* K ⊗ᴸ 𝒪_E/ℓⁿ)` of its reductions, with its canonical comparison map from
`Lg^* K`. We show that `Lg^* K` is derived complete and that this comparison is an isomorphism:
the cone `Lg^* K ⟶ Res_n (red_n (Lg^* K))` of the reduction units is a homotopy limit cone
(`ProEtale.CondensedRing.isHomotopyLimit_reductionTowerCone_leftDerivedUpperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- Blueprint `lemma-inverse-image-tensor-product--5`: on `Dᵇc(-_proét, 𝒪_E)`, the ordinary
inverse image agrees with the completed inverse image. For `g : W ⟶ X` with `W` noetherian and
`K ∈ Dᵇc(X, 𝒪_E)`, the ordinary inverse image `Lg^* K` is derived complete, and the canonical
comparison from `Lg^* K` to its completion `R lim_n Res_n (red_n (Lg^* K))` (the completed
inverse image) is an isomorphism: the cone of the reduction units is a homotopy limit cone. -/
theorem isHomotopyLimit_reductionTowerCone_leftDerivedUpperStar {W X : Scheme.{u}}
    [IsNoetherian W] (g : W ⟶ X)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) K) :
    derivedCompleteIntegers ℓ E W ((L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) ∧
      IsHomotopyLimit
        (reductionTowerCone E ((L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K)) := by
  have h := derivedCompleteIntegers_of_boundedConstructible
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K hK)
  exact ⟨h, isHomotopyLimit_reductionTowerCone h⟩

end AlgebraicGeometry.ProEtale.CondensedRing
