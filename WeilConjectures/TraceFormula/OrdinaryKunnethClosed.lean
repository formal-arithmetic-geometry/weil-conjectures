/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.OrdinaryKunneth
public import WeilConjectures.CategoryTheory.Adjunction.KunnethNatTransPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperProjectionFormula
public import WeilConjectures.TraceFormula.LowerShriekCoherence

/-!
# The ordinary Künneth map and closed pushforwards

For a closed immersion `g : Z ⟶ X`, an open immersion `j : U ⟶ Y` and `N ∈ Dᵇc(Z)⟦ℚ̲̄_ℓ⟧`, the
Künneth map `Rg_* N ⊠ Rj_* B ⟶ R(𝟙 × j)_* (Rg_* N ⊠ B)` (`ProEtale.CondensedRing.openKunnethMap`)
is an isomorphism as soon as the Künneth map of `N` is
(`ProEtale.CondensedRing.isIso_openKunnethMap_lowerStar_of_isClosedImmersion`).

By proper base change along the projections, `Lp_X^* Rg_* N ≅ R(g × 𝟙)_* Lp_Z^* N` on `X ⨯ Y` and
on `X ⨯ U`; by the projection formula for the closed immersions `g × 𝟙` and the identification
`R(𝟙 × j)_* R(g × 𝟙)_* ≅ R(g × 𝟙)_* R(𝟙 × j)_*`, the Künneth map of `Rg_* N` is then `R(g × 𝟙)_*`
of a Künneth map of `N`, up to isomorphisms. This is the abstract statement
`CategoryTheory.Adjunction.isIso_kunnethNatTrans_app_of_pushforward`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable {X Y U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] in
/-- The square of products `(𝟙 × j) ≫ (g × 𝟙) = (g × 𝟙) ≫ (𝟙 × j)` from `Z ⨯ U` to `X ⨯ Y`. -/
lemma commSq_prodMap_prodMap {Z : Over (Spec (.of k))} (g : Z ⟶ X) (j : U ⟶ Y) :
    CommSq (prod.map (𝟙 Z) j) (prod.map g (𝟙 U)) (prod.map g (𝟙 Y)) (prod.map (𝟙 X) j) :=
  ⟨by simp [prod.map_map]⟩

/-- **The Künneth map of a closed pushforward**: for a closed immersion `g : Z ⟶ X`, if the
Künneth map `N ⊠ Rj_* B ⟶ R(𝟙 × j)_* (N ⊠ B)` is an isomorphism, so is the Künneth map
`Rg_* N ⊠ Rj_* B ⟶ R(𝟙 × j)_* (Rg_* N ⊠ B)`. By proper base change and the projection formula for
the closed immersions `g × 𝟙`, the latter is `R(g × 𝟙)_*` of a Künneth map of `N`, up to
isomorphisms (`CategoryTheory.Adjunction.isIso_kunnethNatTrans_app_of_pushforward`). -/
theorem isIso_openKunnethMap_lowerStar_of_isClosedImmersion {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : Z ⟶ X) [IsClosedImmersion g.left] (j : U ⟶ Y) [IsOpenImmersion j.left]
    (N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : IsIso (openKunnethMap ℓ (X := Z) j N B)) :
    IsIso (openKunnethMap ℓ (X := X) j
      ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj N) B) := by
  have hgY : IsClosedImmersion (prod.map g (𝟙 Y)).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id g Y).map (Over.forget _))
      (inferInstanceAs (IsClosedImmersion g.left))
  have hgU : IsClosedImmersion (prod.map g (𝟙 U)).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id g U).map (Over.forget _))
      (inferInstanceAs (IsClosedImmersion g.left))
  have hj : IsIso (boundedConstructibleUpperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j).counit :=
    (Adjunction.Triple.mk
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j)
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        j)).isIso_unit_iff_isIso_counit.1 inferInstance
  have hβY := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ
    (IsPullback.of_prod_fst_with_id g Y)
  have hβU := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ
    (IsPullback.of_prod_fst_with_id g U)
  unfold openKunnethMap at h ⊢
  have : IsIso (openKunnethSecondFactor ℓ (X := X) j B) := by
    unfold openKunnethSecondFactor
    infer_instance
  have : IsIso (openKunnethSecondFactor ℓ (X := Z) j B) := by
    unfold openKunnethSecondFactor
    infer_instance
  refine Adjunction.isIso_kunnethNatTrans_app_of_pushforward _ _
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.map g (𝟙 Y)))
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.map g (𝟙 U)))
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      (commSq_prodMap_prodMap g j))
    (fun A B ↦ boundedConstructiblePullbackSquareComparison_hom_app_δ ℓ
      (commSq_prodMap_prodMap g j) A B)
    _ _ _ _ (asIso ((boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ
      (IsPullback.of_prod_fst_with_id g Y).toCommSq).app N))
    (asIso ((boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ
      (IsPullback.of_prod_fst_with_id g U).toCommSq).app N))
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map g (𝟙 Y))
      prod.snd).symm.app _ ≪≫ eqToIso (by rw [prod.map_snd, Category.comp_id])) h

end AlgebraicGeometry.ProEtale.CondensedRing
