/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeKunnethSquare
public import WeilConjectures.TraceFormula.SourceExchangeKunnethUnit

/-!

# Base change along the Künneth square of a proper morphism

For a proper morphism `f : X ⟶ Y` and `q = f × f : X × X ⟶ Y × Y`, the base change along the
non-cartesian square `q ≫ p₁' = p₁ ≫ f` (the mate of its composition isomorphism) is compared
with the compact-support base changes of the product squares of `X` and `Y` (blueprint
`lem-trf-trace-source-exchange`, Step 3). This is the base-change input of the exceptional
Künneth part of identity (a) of the trace-class source exchange
(`ProEtale.CondensedRing.unit_comp_lowerShriek_map_prodBaseChangeIso`). The comparison goes
through the factorization `q = (1 × f) ≫ (f × 1)` and the cartesian squares
`(f × 1) ≫ p₁' = p_X ≫ f` and `(1 × f) ≫ p_Y = p₂ ≫ f`, using the pasting laws of `Ex_!`
(blueprint `fix-lem-exchanges`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- **Base change along the Künneth square of a proper morphism** (blueprint
`lem-trf-trace-source-exchange`, Step 3): the unit of `Lq^* ⊣ Rq_!` for `q = f × f`, followed by
the composition isomorphism of `q ≫ p₁' = p₁ ≫ f`, the transported counit, the compact-support
base change of the product square of `X` and the counit of `Ra_X! ⊣ Ra_X^!`, is the compact-support
base change of the product square of `Y` followed by `Ra_Y! Rf_* ω_X ≅ Ra_X! ω_X`, the counit of
`Ra_X! ⊣ Ra_X^!` and the unit `𝟙 ⟶ Rf_! 𝟙`. -/
theorem unit_comp_lowerShriek_map_prodBaseChangeIso :
    ((boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
        ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (prod.map f f)).unit.app
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
            ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X)))) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app _) ≫
    (boundedConstructibleLowerShriek _ ℓ f).map
      ((boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X)).map
          (prodUpperStarCounit ℓ (prod.map_snd f f) (dualizingComplex' ℓ X)) ≫
        (prodBaseChangeIso ℓ X X).hom.app (dualizingComplex' ℓ X) ≫
        (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
          ((boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint X)).counit.app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv) =
    ((prodBaseChangeIso ℓ Y Y).hom.app
        ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleUpperStar _ ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriek _ ℓ (toPoint Y)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
              (dualizingComplex' ℓ X)) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (toPoint Y)).inv.app
            (dualizingComplex' ℓ X) ≫
          eqToHom (by rw [comp_toPoint]; rfl) ≫
          (boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint X)).counit.app (𝟙_ _)) ≫
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint Y))).inv) ≫
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app (𝟙_ _) ≫
    (boundedConstructibleLowerShriek _ ℓ f).map
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ f)).inv := by
  sorry
/-- The final step of the exceptional Künneth part of identity (a): after the projection
formula for `f`, the base change along the Künneth square and the unit compatibility of the
projection formula turn `Rf_!` of the evaluation into the evaluation on `Y`. -/
theorem whiskerRight_unit_square_comp_exceptionalProjection :
    (((boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
          ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
            (prod.map f f)).unit.app
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X)))) ≫
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app _) ▷
          (boundedConstructibleLowerStar _ ℓ f).obj K) ≫
      boundedConstructibleExceptionalProjectionMorphism _ ℓ f _ _ ≫
      (boundedConstructibleLowerShriek _ ℓ f).map
        ((((boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X)).map
            (prodUpperStarCounit ℓ (prod.map_snd f f) (dualizingComplex' ℓ X)) ≫
          (prodBaseChangeIso ℓ X X).hom.app (dualizingComplex' ℓ X) ≫
          (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
            ((boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint X)).counit.app (𝟙_ _)) ≫
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv) ▷ _) ≫
        (𝟙_ _ ◁ ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app K :
          (boundedConstructibleUpperStar _ ℓ f).obj ((boundedConstructibleLowerStar _ ℓ f).obj K) ⟶ K)) ≫
        (λ_ K).hom) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K =
    (((prodBaseChangeIso ℓ Y Y).hom.app
        ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X)) ≫
      (boundedConstructibleUpperStar _ ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriek _ ℓ (toPoint Y)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
              (dualizingComplex' ℓ X)) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (toPoint Y)).inv.app
            (dualizingComplex' ℓ X) ≫
          eqToHom (by rw [comp_toPoint]; rfl) ≫
          (boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint X)).counit.app (𝟙_ _))) ▷ _) ≫
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint Y))).inv ▷ _) ≫
    (λ_ _).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
