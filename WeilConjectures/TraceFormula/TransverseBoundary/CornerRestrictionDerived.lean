/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianDerivedGlobalExtPullback
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerRestriction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# The restriction to the punctured trait at a transverse corner, in the derived category

Let `S` be the strict localization of the surface `Z` of a transverse corner
(`AlgebraicGeometry.Scheme.TransverseCorner`) at a geometric point `z̄` over the corner point,
`X_S, Y_S` the two transverse divisors and `ℓ` a prime invertible in `k`. The restriction map
`RΓ(S - Y_S, ℤ/ℓ) ⟶ RΓ(X_S - z, ℤ/ℓ)` of derived global sections is an isomorphism in `D⁺(Ab)`.

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.isIso_rightDerivedFunctorPlus_puncturedTraitι`.

## Implementation details

The restriction map is the derived pullback of global sections: `RΓ(S - Y_S, -)` applied to the
derived unit of `ι^* ⊣ ι_*`, followed by the Leray identification `RΓ(S - Y_S, Rι_* -) ≅
RΓ(X_S - z, -)`. Its homology in degree `q ≥ 0` is the comparison map `Etale.cohomologyMap`
(`AlgebraicGeometry.Etale.exists_addEquiv_derivedGlobal_ext_pullback`), which is bijective
(`AlgebraicGeometry.Scheme.TransverseCorner.bijective_cohomologyMap_puncturedTraitι`); in
negative degrees both sides vanish.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] [IsAlgClosed k] (C : TransverseCorner k) {Ω : Type u} [Field Ω]
  [IsAlgClosed Ω] (zbar : Spec (.of Ω) ⟶ C.Z) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
  (hz : Set.range zbar = {C.z})

include hℓ hz in
/-- The restriction map `RΓ(S - Y_S, ℤ/ℓ) ⟶ RΓ(X_S - z, ℤ/ℓ)` of derived global sections at a
transverse corner is an isomorphism in `D⁺(Ab)`: it is the derived pullback of global sections
along the closed immersion `X_S - z ⟶ S - Y_S` of the punctured trait. -/
theorem isIso_rightDerivedFunctorPlus_puncturedTraitι :
    let g := C.puncturedTraitι zbar
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((C.puncturedStrictLocalization zbar).constantZMod ℓ)
    IsIso ((Sheaf.Γ (C.puncturedStrictLocalization zbar).smallEtaleTopology
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).derivedPlus.unit.app K) ≫
      (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Etale.lowerStar AddCommGrpCat.{u + 1} g)
        (Sheaf.Γ (C.puncturedStrictLocalization zbar).smallEtaleTopology
          AddCommGrpCat.{u + 1}) _ _ _ _
        (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
          (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g))
        (Etale.lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g)).hom.app
          (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K)) := by
  intro g K
  refine (isIso_iff_of_reflects_iso _ DerivedCategory.Plus.ι).1
    ((DerivedCategory.isIso_iff _ _).2 fun n ↦ ?_)
  change IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map _)
  rcases lt_or_ge n 0 with hn | hn
  · refine ⟨0, ?_, ?_⟩ <;> refine IsZero.eq_of_src ?_ _ _
    · exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ K 0 hn
    · refine IsZero.of_iso
        (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
          (Sheaf.Γ (C.puncturedTrait zbar).smallEtaleTopology AddCommGrpCat.{u + 1})
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (((g)^*[AddCommGrpCat.{u + 1}]).obj
              ((C.puncturedStrictLocalization zbar).constantZMod ℓ))) 0 hn) ?_
      exact (DerivedCategory.Plus.homologyFunctor _ n).mapIso
        ((Sheaf.Γ _ AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.mapIso
          ((((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).app _))
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    obtain ⟨b₁, b₂, h⟩ := Etale.exists_addEquiv_derivedGlobal_ext_pullback g
      ((C.puncturedStrictLocalization zbar).constantZMod ℓ) q
    refine (ConcreteCategory.isIso_iff_bijective _).2
      ((Function.Bijective.of_comp_iff' b₂.bijective _).1 ?_)
    have e : ∀ x, (⇑b₂ ∘ _) x = (Etale.cohomologyMap g _ q ∘ b₁) x := h
    rw [funext e]
    exact (C.bijective_cohomologyMap_puncturedTraitι zbar hℓ hz q).comp b₁.bijective

end AlgebraicGeometry.Scheme.TransverseCorner
