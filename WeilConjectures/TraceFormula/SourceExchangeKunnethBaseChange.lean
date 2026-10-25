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

section Pasting

variable {S P W V : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

set_option maxHeartbeats 1000000 in
-- the pasting identities are checked against the six-functor definitions
/-- The compact-support base changes of the product squares of `X` and `Y` (here abstract
cartesian squares over a base `S`) are compatible along a proper `f : X ⟶ Y`: pasting the
cartesian squares `h ≫ p₁' = p_X ≫ f` and `g ≫ p_Y = p₂ ≫ f` with the product squares,
`Ex_!` of the square of `X` is read off from `Ex_!` of the square of `Y`. -/
theorem lowerShriekBaseChange_inv_app_paste (aX : X ⟶ S) (aY : Y ⟶ S) (hA : f ≫ aY = aX)
    {pX : P ⟶ X} {pY : P ⟶ Y} {p₁ p₂ : W ⟶ X} {p₁' p₂' : V ⟶ Y} {g : W ⟶ P} {h : P ⟶ V}
    (hp : g ≫ pX = p₁) (hpY : h ≫ p₂' = pY) (sqY : IsPullback p₂' p₁' aY aY)
    (sqXY : IsPullback pY pX aY aX) (sqX : IsPullback p₂ p₁ aX aX) (s₁ : IsPullback h pX p₁' f)
    (s₃ : IsPullback p₂ g f pY) (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY).app
      ((boundedConstructibleLowerStar _ ℓ f).obj B))]
    [IsIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqX).app B)] :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s₁).app
        ((boundedConstructibleUpperStar _ ℓ p₂').obj ((boundedConstructibleLowerStar _ ℓ f).obj B)) ≫
      (boundedConstructibleLowerShriek _ ℓ pX).map
        ((boundedConstructibleUpperStarComp _ ℓ h p₂').inv.app
            ((boundedConstructibleLowerStar _ ℓ f).obj B) ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj
            ((boundedConstructibleLowerStar _ ℓ f).obj B)) hpY) ≫
          (boundedConstructibleUpperStar _ ℓ pY).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B) ≫
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s₃).app B) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g pX).inv.app
        ((boundedConstructibleUpperStar _ ℓ p₂).obj B) ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj
        ((boundedConstructibleUpperStar _ ℓ p₂).obj B)) hp) ≫
      inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqX).app B) =
    (boundedConstructibleUpperStar _ ℓ f).map
        (inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY).app
          ((boundedConstructibleLowerStar _ ℓ f).obj B))) ≫
      (boundedConstructibleUpperStarComp _ ℓ f aY).inv.app _ ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj
        ((boundedConstructibleLowerShriek _ ℓ aY).obj
          ((boundedConstructibleLowerStar _ ℓ f).obj B))) hA) ≫
      (boundedConstructibleUpperStar _ ℓ aX).map
        ((boundedConstructibleLowerShriek _ ℓ aY).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY).inv.app B ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek _ ℓ r).obj B) hA)) := by
  subst hA hp hpY
  have hV : (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqX).app B = _ :=
    boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert ℓ s₃ sqXY B
  have hH : (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqXY).app
      ((boundedConstructibleLowerShriek _ ℓ f).obj B) = _ :=
    boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ s₁ sqY _
  have nY := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY).naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B)
  have n₁ := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ s₁).naturality
    ((boundedConstructibleUpperStar _ ℓ p₂').map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B))
  have nC := (boundedConstructibleUpperStarComp _ ℓ f aY).hom.naturality
    ((boundedConstructibleLowerShriek _ ℓ aY).map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B))
  have nC' := (boundedConstructibleUpperStarComp _ ℓ h p₂').inv.naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B)
  simp only [Functor.comp_map, Functor.comp_obj] at nY n₁ nC nC'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id]
  simp only [← Category.assoc]
  rw [IsIso.comp_inv_eq]
  simp only [Category.assoc]
  rw [hV, hH]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have c₁ : (boundedConstructibleUpperStar _ ℓ (f ≫ aY)).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY).inv.app B) ≫
      (boundedConstructibleUpperStar _ ℓ (f ≫ aY)).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f aY).hom.app B) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have c₂ : (boundedConstructibleUpperStar _ ℓ f).map
        (inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY).app
          ((boundedConstructibleLowerStar _ ℓ f).obj B))) ≫
      (boundedConstructibleUpperStar _ ℓ f).map ((boundedConstructibleUpperStar _ ℓ aY).map
        ((boundedConstructibleLowerShriek _ ℓ aY).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B))) ≫
      (boundedConstructibleUpperStar _ ℓ f).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sqY).app
          ((boundedConstructibleLowerShriek _ ℓ f).obj B)) =
      (boundedConstructibleUpperStar _ ℓ f).map ((boundedConstructibleLowerShriek _ ℓ p₁').map
        ((boundedConstructibleUpperStar _ ℓ p₂').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B))) := by
    rw [← Functor.map_comp, ← Functor.map_comp, nY, IsIso.inv_hom_id_assoc]
  have c₃ : (boundedConstructibleLowerShriek _ ℓ pX).map ((boundedConstructibleUpperStar _ ℓ h).map
        ((boundedConstructibleUpperStar _ ℓ p₂').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B))) ≫
      (boundedConstructibleLowerShriek _ ℓ pX).map
        ((boundedConstructibleUpperStarComp _ ℓ h p₂').inv.app
          ((boundedConstructibleLowerShriek _ ℓ f).obj B)) =
      (boundedConstructibleLowerShriek _ ℓ pX).map
          ((boundedConstructibleUpperStarComp _ ℓ h p₂').inv.app
            ((boundedConstructibleLowerStar _ ℓ f).obj B)) ≫
        (boundedConstructibleLowerShriek _ ℓ pX).map
          ((boundedConstructibleUpperStar _ ℓ (h ≫ p₂')).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, nC']
  simp only [reassoc_of% c₁, Category.id_comp]
  rw [reassoc_of% nC, Iso.inv_hom_id_app_assoc, reassoc_of% c₂, reassoc_of% n₁, reassoc_of% c₃]

end Pasting

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
