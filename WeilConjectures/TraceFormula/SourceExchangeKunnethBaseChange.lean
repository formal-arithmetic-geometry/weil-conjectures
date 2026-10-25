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
      ((boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app _ : _ ⟶ (boundedConstructibleLowerShriek _ ℓ f).obj ((boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj ((boundedConstructibleUpperStar _ ℓ (prod.map f f)).obj ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X))))))) ≫
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
/-- An abstract chain of identities in monoidal categories: through a functor `F`, a map
`U ▷ M` followed by `P` and `F` of an evaluation `θ` is rewritten, given the naturality of `P`
in `θ`, a factorization of `U ≫ F θ`, the unit compatibility of `P₁` and a triangle identity. -/
lemma _root_.CategoryTheory.Functor.whiskerRight_comp_map_comp_eq {𝒳 𝒟 : Type*} [Category 𝒳]
    [Category 𝒟] [MonoidalCategory 𝒳] [MonoidalCategory 𝒟] (F : 𝒳 ⥤ 𝒟) {R M' K N : 𝒳}
    {A B₁ B₂ M : 𝒟} {U : A ⟶ F.obj R} {θ : R ⟶ 𝟙_ 𝒳} {e : M' ⟶ K}
    {P : F.obj R ⊗ M ⟶ F.obj (R ⊗ M')} {P₁ : F.obj (𝟙_ 𝒳) ⊗ M ⟶ F.obj (𝟙_ 𝒳 ⊗ M')}
    {φ₁ : A ⟶ B₁} {φ₂ : B₁ ⟶ B₂} {ε' : B₂ ⟶ 𝟙_ 𝒟} {η₁ : 𝟙_ 𝒟 ⟶ F.obj N}
    {ε₂ : N ⟶ 𝟙_ 𝒳} {ηM : M ⟶ F.obj M'} {r : F.obj K ⟶ M}
    (hP : P ≫ F.map (θ ▷ M') = (F.map θ ▷ M) ≫ P₁)
    (hB : U ≫ F.map θ = (φ₁ ≫ φ₂ ≫ ε') ≫ η₁ ≫ F.map ε₂)
    (hU : ((η₁ ≫ F.map ε₂) ▷ M) ≫ P₁ ≫ F.map (λ_ M').hom = (λ_ M).hom ≫ ηM)
    (hT : ηM ≫ F.map e ≫ r = 𝟙 M) :
    (U ▷ M) ≫ P ≫ F.map ((θ ▷ M') ≫ (𝟙_ 𝒳 ◁ e) ≫ (λ_ K).hom) ≫ r =
      ((φ₁ ≫ φ₂) ▷ M) ≫ (ε' ▷ M) ≫ (λ_ M).hom := by
  have hU' := hU =≫ (F.map e ≫ r)
  simp only [Category.assoc, hT, Category.comp_id, comp_whiskerRight] at hU'
  have hB' : (U ▷ M) ≫ (F.map θ ▷ M) = ((φ₁ ≫ φ₂ ≫ ε') ▷ M) ≫ ((η₁ ≫ F.map ε₂) ▷ M) := by
    rw [← comp_whiskerRight, hB, comp_whiskerRight]
  rw [leftUnitor_naturality]
  simp only [F.map_comp, Category.assoc, reassoc_of% hP, reassoc_of% hB', hU', comp_whiskerRight]

/-- The triangle identity for `Lf^* ⊣ Rf_!` read through `Rf_! ≅ Rf_*`: the unit at `Rf_* K`
followed by `Rf_!` of the counit of `Lf^* ⊣ Rf_*` is `Rf_* K ≅ Rf_! K` inverted. -/
lemma unit_app_comp_lowerShriek_map_counit_app_comp_hom_app :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app
        ((boundedConstructibleLowerStar _ ℓ f).obj K) ≫
      (boundedConstructibleLowerShriek _ ℓ f).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app K :
          (boundedConstructibleUpperStar _ ℓ f).obj ((boundedConstructibleLowerStar _ ℓ f).obj K) ⟶
            K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K = 𝟙 _ := by
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  have hn := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).counit.app K)
  rw [← reassoc_of% hn, Iso.inv_hom_id_app]
  rw [Category.comp_id]
  exact (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f).right_triangle_components K

/-- The final step of the exceptional Künneth part of identity (a): after the projection
formula for `f`, the base change along the Künneth square and the unit compatibility of the
projection formula turn `Rf_!` of the evaluation into the evaluation on `Y`. -/
theorem whiskerRight_unit_square_comp_exceptionalProjection :
    (((boundedConstructibleLowerShriek _ ℓ (prod.fst : Y ⨯ Y ⟶ Y)).map
          ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ
            (prod.map f f)).unit.app
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj
              ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X)))) ≫
        ((boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (prod.map_fst f f)).hom.app _ : _ ⟶ (boundedConstructibleLowerShriek _ ℓ f).obj ((boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj ((boundedConstructibleUpperStar _ ℓ (prod.map f f)).obj ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).obj ((boundedConstructibleLowerStar _ ℓ f).obj (dualizingComplex' ℓ X))))))) ▷
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
  have hP := (boundedConstructibleExceptionalProjectionMorphism_natural_left _ ℓ f
    ((boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ X ⟶ X)).map
        (prodUpperStarCounit ℓ (prod.map_snd f f) (dualizingComplex' ℓ X)) ≫
      (prodBaseChangeIso ℓ X X).hom.app (dualizingComplex' ℓ X) ≫
      (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
        ((boundedConstructibleUpperShriekAdjunction _ ℓ (toPoint X)).counit.app (𝟙_ _)) ≫
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv)
    ((boundedConstructibleLowerStar _ ℓ f).obj K)).symm
  have hB := unit_comp_lowerShriek_map_prodBaseChangeIso ℓ f
  have hU := whiskerRight_unit_comp_exceptionalProjection_tensorUnit ℓ f
    ((boundedConstructibleLowerStar _ ℓ f).obj K)
  have hT := unit_app_comp_lowerShriek_map_counit_app_comp_hom_app ℓ f K
  apply Functor.whiskerRight_comp_map_comp_eq (boundedConstructibleLowerShriek _ ℓ f)
  case hP => exact hP
  case hB => exact hB
  case hU => exact hU
  case hT => exact hT

end AlgebraicGeometry.ProEtale.CondensedRing
