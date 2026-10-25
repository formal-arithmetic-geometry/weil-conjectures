/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.TraceFormula.GenericBaseChange

/-!

# Ordinary Künneth formula along an open immersion

Let `X, Y` be separated `k`-schemes of finite type, `j : U ⟶ Y` an open immersion and
`G = 𝟙_X × j : X ⨯ U ⟶ X ⨯ Y`. For `M ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and `B ∈ Dᵇc(U)⟦ℚ̲̄_ℓ⟧` the *Künneth map*
```
M ⊠ Rj_* B = Lp_X^* M ⊗ᴸ Lp_Y^* Rj_* B ⟶ RG_* (M ⊠ B)
```
(`ProEtale.CondensedRing.openKunnethMap`) is the adjoint, for `LG^* ⊣ RG_*`, of the monoidal
structure of `LG^*`, the composition isomorphisms `LG^* Lp_X^* ≅ Lp_X^*` and
`LG^* Lp_Y^* ≅ Lp_U^* Lj^*`, and the counit `Lj^* Rj_* B ⟶ B`.

## Main statements

- `ProEtale.CondensedRing.isIso_exchangeRight_prodMapUpperStarSndIso`,
  `ProEtale.CondensedRing.isIso_homEquiv_prodMapUpperStarSndIso_hom_app_comp_map_counit`: the
  transpose `Lp_Y^* Rj_* B ⟶ RG_* Lp_U^* B` of the second factor of the Künneth map is the base
  change morphism of the square `commSq_prodMap_snd`, hence an isomorphism by generic base change.
  Together with `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_of_isDualizable` this is
  the mathematical content of the Künneth formula for dualizable `M`; the instantiation for
  `openKunnethMap` itself is not formalized yet (see the implementation notes).

## Sorried inputs

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap`: generic base change
  over the field `k` (SGA 4½, [Th. finitude], Théorème 1.9 over `Spec k`; Bhatt–Scholze §6.8
  for `ℚ̄_ℓ`-coefficients; blueprint `sk-lem-tf-independent-base-change`): base change along
  `X ⨯ Y ⟶ Y` commutes with `Rf_*`.
- `ProEtale.CondensedRing.isIso_openKunnethMap`: the Künneth map is an isomorphism (blueprint
  `lem-trf-ordinary-kunneth`; SGA 4½, [Th. finitude], Corollaire 1.11). For dualizable `M` it
  follows formally from generic base change and the projection formula at the dualizable object
  `Lp_X^* M`. For general `M` it does not: a dévissage in `M` (restriction to strata on which
  `M` is lisse) needs the exchange `R(j' × 1)_! ∘ R(1 × j)_* ≅ R(1 × j)_* ∘ R(j' × 1)_!`, which
  is itself a Künneth formula.

## Implementation notes

Unfolding `openKunnethMap` produces terms (from the unfolding of `externalProduct` and from the
auxiliary proofs of the definition) which differ from separately elaborated terms only in their
proofs; matching its second factor against the generic lemmas then makes the kernel unfold the
six functors (deterministic timeouts even at `maxHeartbeats 800000`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

/-- The composition isomorphism `L(𝟙 × j)^* Lp_X^* ≅ Lp_X^*` for the projections of `X ⨯ Y` and
`X ⨯ U`. -/
noncomputable def prodMapUpperStarFstIso (j : U ⟶ Y) :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.fst : X ⨯ Y ⟶ X) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.fst : X ⨯ U ⟶ X) :=
  (boundedConstructibleUpperStarComp _ ℓ (prod.map (𝟙 X) j) prod.fst).symm ≪≫
    eqToIso (by rw [prod.map_fst, Category.comp_id])

/-- The composition isomorphism `L(𝟙 × j)^* Lp_Y^* ≅ Lp_U^* Lj^*` for the projections of `X ⨯ Y`
and `X ⨯ U`. -/
noncomputable def prodMapUpperStarSndIso (j : U ⟶ Y) :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ U ⟶ U) :=
  (boundedConstructibleUpperStarComp _ ℓ (prod.map (𝟙 X) j) prod.snd).symm ≪≫
    eqToIso (by rw [prod.map_snd]) ≪≫ boundedConstructibleUpperStarComp _ ℓ prod.snd j

/-- The *Künneth map* `M ⊠ Rj_* B ⟶ R(𝟙 × j)_* (M ⊠ B)` for an open immersion `j : U ⟶ Y`: the
adjoint, for `L(𝟙 × j)^* ⊣ R(𝟙 × j)_*`, of the monoidal structure of `L(𝟙 × j)^*`, the
composition isomorphisms of the pullbacks and the counit `Lj^* Rj_* B ⟶ B`. -/
noncomputable def openKunnethMap (j : U ⟶ Y) (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ (Y := Y) M
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj B) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map (𝟙 X) j)).obj (externalProduct ℓ M B) :=
  (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (prod.map (𝟙 X) j)).homEquiv _ _
    ((Functor.Monoidal.μIso _ _ _).inv ≫
      ((prodMapUpperStarFstIso ℓ j).hom.app M ⊗ₘ
        ((prodMapUpperStarSndIso ℓ j).hom.app _ ≫
          (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ U ⟶ U)).map
            ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ j).counit.app B))))

/-- **The ordinary Künneth formula along an open immersion**, at the coefficient stage `ℚ̄_ℓ`
(blueprint `lem-trf-ordinary-kunneth`, section `sec-six-functors`, states it for finite
coefficients and a general morphism `f`; here `f = j` is an open immersion). For an open immersion
`j : U ⟶ Y`, `M ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` and `B ∈ Dᵇc(U)⟦ℚ̲̄_ℓ⟧`, the Künneth map
`M ⊠ Rj_* B ⟶ R(𝟙 × j)_* (M ⊠ B)` is an isomorphism (SGA 4½, [Th. finitude], Corollaire 1.11,
a consequence of Deligne's generic base change theorem, [Th. finitude], Théorème 1.9; for
`ℚ̄_ℓ`-coefficients by passage to the limit, Bhatt–Scholze, Section 6.8). -/
theorem isIso_openKunnethMap (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (openKunnethMap ℓ j M B) :=
  sorry


/-- `prodMapUpperStarSndIso` is the pullback comparison of the square `commSq_prodMap_snd`. -/
lemma prodMapUpperStarSndIso_eq_pullbackSquareComparison (j : U ⟶ Y) :
    prodMapUpperStarSndIso ℓ (X := X) j =
      boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (commSq_prodMap_snd j) :=
  rfl

/-- The exchange morphism `Lp_Y^* Rj_* ⟶ R(𝟙 × j)_* Lp_U^*` of `prodMapUpperStarSndIso` is an
isomorphism: it is the base change morphism of the square `commSq_prodMap_snd`, an isomorphism by
generic base change (`isIso_boundedConstructibleBaseChange_prodMap`). -/
lemma isIso_exchangeRight_prodMapUpperStarSndIso (j : U ⟶ Y) :
    IsIso (Adjunction.exchangeRight
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j)
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map (𝟙 X) j))
      (prodMapUpperStarSndIso ℓ (X := X) j)) := by
  rw [prodMapUpperStarSndIso_eq_pullbackSquareComparison,
    ← boundedConstructibleBaseChange_eq_exchangeRight]
  exact isIso_boundedConstructibleBaseChange_prodMap ℓ j

/-- The transpose `Lp_Y^* Rj_* B ⟶ R(𝟙 × j)_* Lp_U^* B` of the second factor of the Künneth map,
the counit of `Lj^* ⊣ Rj_*` transported along `prodMapUpperStarSndIso`, is an isomorphism: it is
the exchange morphism of `prodMapUpperStarSndIso`
(`isIso_exchangeRight_prodMapUpperStarSndIso`). -/
lemma isIso_homEquiv_prodMapUpperStarSndIso_hom_app_comp_map_counit (j : U ⟶ Y)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.map (𝟙 X) j)).homEquiv
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ Y ⟶ Y)).obj
          ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj B))
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).obj B)
        ((prodMapUpperStarSndIso ℓ (X := X) j).hom.app
          ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj B) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            j).counit.app B))) := by
  have := isIso_exchangeRight_prodMapUpperStarSndIso ℓ (X := X) j
  rw [Adjunction.homEquiv_hom_app_comp_map_counit]
  exact NatIso.isIso_app_of_isIso _ B

end AlgebraicGeometry.ProEtale.CondensedRing
