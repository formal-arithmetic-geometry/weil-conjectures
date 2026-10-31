/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.OrdinaryKunneth
public import WeilConjectures.TraceFormula.ProperKunneth
public import WeilConjectures.TraceFormula.OrdinaryKunnethClosed

/-!

# The ordinary Künneth map and proper pushforward in the first factor: composites

Let `j : U ⟶ Y` be an open immersion and `g : Z ⟶ X` a proper morphism of separated `k`-schemes
of finite type. For `N ∈ Dᵇc(Z)⟦ℚ̲̄_ℓ⟧` and `B ∈ Dᵇc(U)⟦ℚ̲̄_ℓ⟧`, if the Künneth map
`κ_Z(N, B) : N ⊠ Rj_* B ⟶ R(𝟙 × j)_* (N ⊠ B)` (`ProEtale.CondensedRing.openKunnethMap`) is an
isomorphism, so is `κ_X(Rg_* N, B)`
(`ProEtale.CondensedRing.isIso_openKunnethMap_lowerStar_of_isProper`).

## Proof

The second factor of the Künneth map has invertible transpose (generic base change,
`ProEtale.CondensedRing.isIso_exchangeRight_prodMapUpperStarSndIso`), so `κ_X(M, B)` is an
isomorphism if and only if the left projection morphism
`Lp_X^* M ⊗ R(𝟙 × j)_* Lp_U^* B ⟶ R(𝟙 × j)_* (L(𝟙 × j)^* Lp_X^* M ⊗ Lp_U^* B)` is
(`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_iff_isIso_leftProjectionMorphism`).
These left projection morphisms are compared
(`ProEtale.CondensedRing.isIso_leftProjectionMorphism_prodMap_lowerStar`) through the Künneth map
of `q = g × j : Z ⨯ U ⟶ X ⨯ Y`, the transpose along `Lq^* ⊣ Rq_*` of
```
Lq^* (Lp_X^* Rg_* N ⊗ Lp_Y^* Rj_* B) ⟶ Lq^* Lp_X^* Rg_* N ⊗ Lq^* Lp_Y^* Rj_* B ⟶ Lp_Z^* N ⊗ Lp_U^* B
```
built from the transported counits (`ProEtale.CondensedRing.prodUpperStarCounit`), decomposed
along the two factorizations of `q`:

* `q = (g × 𝟙_U) ≫ (𝟙_X × j)`: by `CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq` it is the
  left projection morphism of `𝟙_X × j` at `(Lp_X^* Rg_* N, Lp_U^* B)` up to proper and generic
  base change morphisms and the proper projection formula for `g × 𝟙_U`
  (`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_iff_of_isIso`);
* `q = (𝟙_Z × j) ≫ (g × 𝟙_Y)`: by the mirrored decomposition
  `CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq_right` it is `R(g × 𝟙_Y)_*` of the left
  projection morphism of `𝟙_Z × j` at `(Lp_Z^* N, Lp_U^* B)` up to the same kind of isomorphisms
  (`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso_right`).

## Implementation notes

The Künneth maps are only compared through abstract lemmas instantiated by unification: terms
obtained by unfolding definitions contain auxiliary proof constants and `eqToHom`s, and comparing
them with separately elaborated terms makes the elaborator and the kernel unfold large terms.

This module holds the abstract decompositions of the Künneth map of a composite and the first
comparison, along `q = (𝟙_Z × j) ≫ (g × 𝟙_Y)`; the rest of the proof is in
`WeilConjectures.TraceFormula.OrdinaryKunnethClosed` (split for compile time).

## Main statements

- `ProEtale.CondensedRing.isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_prodMap_id_comp`

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

open Functor.OplaxMonoidal

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  {R' : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} (adjR : R' ⊣ R)
  {S' : C₃ ⥤ C₂} {S : C₂ ⥤ C₃} (adjS : S' ⊣ S)
  {Q' : C₃ ⥤ C₁} {Q : C₁ ⥤ C₃} (adjQ : Q' ⊣ Q)
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃] [R'.OplaxMonoidal]
  [S'.OplaxMonoidal] [Q'.OplaxMonoidal]

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

-- the tensor products are elaborated through the monoidal category instance, as in
-- `WeilConjectures.TraceFormula.OrdinaryKunneth`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable {X Y U Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
set_option maxHeartbeats 1000000 in
-- the instantiation of the abstract lemmas involves large terms
/-- **The Künneth map of `g × j` along `(𝟙 × j) ≫ (g × 𝟙)`**: for a proper `g : Z ⟶ X`, if the
left projection morphism of `L(𝟙_Z × j)^* ⊣ R(𝟙_Z × j)_*` at `(Lp_Z^* N, Lp_U^* B)` is an
isomorphism, so is the Künneth map of `(𝟙_Z × j) ≫ (g × 𝟙_Y)` built from the transported counits
(`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso_right`); the remaining comparison
maps are proper and generic base change morphisms and proper projection morphisms. -/
lemma isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_prodMap_id_comp (g : Z ⟶ X)
    [IsProper g.left] (j : U ⟶ Y) (N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (w₁' : (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y)) ≫ prod.fst =
      (prod.map (𝟙 Z) j ≫ prod.fst) ≫ g)
    (w₂' : (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y)) ≫ prod.snd = prod.snd ≫ j)
    (h : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (prod.map (𝟙 Z) j)).leftProjectionMorphism
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.fst : Z ⨯ Y ⟶ Z)).obj N)
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : Z ⨯ U ⟶ U)).obj B))) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction
      ℓ (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y))).homEquiv _ _
      (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y))) _ _ ≫
        (prodUpperStarCounit ℓ w₁' N ⊗ₘ prodUpperStarCounit ℓ w₂' B))) := by
  have := isProper_prodMap_id (W := Y) g
  have hsnd : prod.map g (𝟙 Y) ≫ (prod.snd : X ⨯ Y ⟶ Y) = prod.snd := by simp
  have w₂'' : prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y) ≫ (prod.snd : X ⨯ Y ⟶ Y) = prod.snd ≫ j := by
    simp
  have sqY := IsPullback.of_prod_fst_with_id g Y
  have := isIso_homEquiv_prodUpperStarCounit ℓ sqY N
  have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction
      ℓ (prod.map (𝟙 Z) j)).homEquiv _ _
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map (𝟙 Z) j) (prod.map g (𝟙 Y))).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ prod.snd).obj
          ((boundedConstructibleLowerStar ℓ j).obj B)) ≫
        prodUpperStarCounit ℓ w₂' B)) := by
    rw [upperStarComp_inv_app_comp_prodUpperStarCounit_right ℓ w₂' w₂'' B,
      Adjunction.homEquiv_naturality_left]
    have := isIso_homEquiv_prodUpperStarCounit_of_eq_snd ℓ (X := Z) j hsnd w₂'' B
    infer_instance
  exact Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso_right
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map (𝟙 Z) j))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map g (𝟙 Y))) _
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ _ _)
    (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ _ _) _ _ _
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.map (𝟙 Z) j) prod.fst).inv.app N)
    (upperStarComp_inv_app_comp_prodUpperStarCounit_left ℓ w₁' sqY.w.symm N)

end AlgebraicGeometry.ProEtale.CondensedRing
