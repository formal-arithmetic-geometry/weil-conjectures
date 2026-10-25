/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

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

## Sorried input

- `ProEtale.CondensedRing.isIso_openKunnethMap`: the Künneth map is an isomorphism (blueprint
  `lem-trf-ordinary-kunneth`; SGA 4½, [Th. finitude], Corollaire 1.11). It rests on Deligne's
  generic base change theorem over `Spec k` ([Th. finitude], Théorème 1.9), which handles a
  dualizable `M` through the projection formula at `Lp_X^* M`
  (`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_exchangeRight_of_isDualizable`). For
  general `M`, a dévissage in `M` needs the exchange
  `R(j' × 1)_! ∘ R(1 × j)_* ≅ R(1 × j)_* ∘ R(j' × 1)_!`, itself a Künneth formula.

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


omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom]
  [QuasiCompact U.hom] [IsSeparated U.hom] in
/-- The commutative square
```
X ⨯ U ──(𝟙 × f)──▶ X ⨯ Y
  │ p_U               │ p_Y
  ▼                   ▼
  U ────── f ───────▶ Y
```
of the second projections, the base change of `f` along `X ⨯ Y ⟶ Y`. -/
lemma commSq_prodMap_snd (f : U ⟶ Y) :
    CommSq (prod.snd : X ⨯ U ⟶ U) (prod.map (𝟙 X) f) f prod.snd :=
  ⟨(prod.map_snd _ _).symm⟩

/-- `prodMapUpperStarSndIso` is the pullback comparison of the square `commSq_prodMap_snd`. -/
lemma prodMapUpperStarSndIso_eq_pullbackSquareComparison (j : U ⟶ Y) :
    prodMapUpperStarSndIso ℓ (X := X) j =
      boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (commSq_prodMap_snd j) :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
