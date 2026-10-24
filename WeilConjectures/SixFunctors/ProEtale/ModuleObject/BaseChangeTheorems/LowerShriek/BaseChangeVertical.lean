/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionTriangle

/-!

# Vertical pasting of the compact-support base change

For cartesian squares `sq₁ : IsPullback h v₁ v₂ k` and `sq₂ : IsPullback k w₁ w₂ l` of separated
`k`-schemes of finite type, the compact-support base change `Ex_!` of the outer rectangle on
bounded constructible `ℚ̄_ℓ`-sheaves is the horizontal composite of those of the two squares,
through the composition isomorphisms `R(v₂ ≫ w₂)_! ≅ Rv₂_! ⋙ Rw₂_!` and
`R(v₁ ≫ w₁)_! ≅ Rv₁_! ⋙ Rw₁_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert'`,
blueprint `fix-lem-exchanges`, item (2)).

The proof computes all the compact-support base changes through the triangle of compactifications
`T₂` defining the composition isomorphism of `(v₂, w₂)` and its base change `T₁'` along the two
squares (`Compactification.Triangle.ofIsPullback`), on which the exchange maps are compatible
with the composition isomorphisms of the triangles
(`CategoryTheory.ExchangeFormalism.compIso_shriekBaseChange`), and uses that the composition
isomorphism of `(v₁, w₁)` can be computed through `T₁'`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

/-- The 2-categorical computation behind the vertical pasting of the compact-support base change:
conjugating the exchange maps of a pair of triangles by comparison isomorphisms. -/
lemma CategoryTheory.TwoSquare.vertical_pasting_aux {A B C A' B' C' : Type*} [Category* A]
    [Category* B] [Category* C] [Category* A'] [Category* B'] [Category* C'] {V₂ : A ⥤ B}
    {W₂ : B ⥤ C} {U₂ U₂T : A ⥤ C} {V₁ V₁T : A' ⥤ B'} {W₁ W₁T : B' ⥤ C'} {U₁ U₁T : A' ⥤ C'}
    {Lh : A ⥤ A'} {Lk : B ⥤ B'} {Ll : C ⥤ C'} (iU₂ : U₂ ≅ U₂T) (cT₂ : V₂ ⋙ W₂ ≅ U₂T)
    (iU₁ : U₁ ≅ U₁T) (cT₁ : V₁T ⋙ W₁T ≅ U₁T) (iV₁ : V₁T ≅ V₁) (iW₁ : W₁T ≅ W₁)
    (SU : U₂T ⋙ Ll ⟶ Lh ⋙ U₁T) (SV : V₂ ⋙ Lk ⟶ Lh ⋙ V₁T) (SW : W₂ ⋙ Ll ⟶ Lk ⋙ W₁T)
    (h : Functor.whiskerRight cT₂.hom Ll ≫ SU =
      (TwoSquare.hComp (T := V₂) (B := V₁T) SV SW).natTrans ≫ Functor.whiskerLeft Lh cT₁.hom) :
    Functor.whiskerRight iU₂.hom Ll ≫ SU ≫ Functor.whiskerLeft Lh iU₁.inv =
      Functor.whiskerRight (iU₂ ≪≫ cT₂.symm).hom Ll ≫
        (TwoSquare.hComp (T := V₂) (B := V₁) (SV ≫ Functor.whiskerLeft Lh iV₁.hom)
          (SW ≫ Functor.whiskerLeft Lk iW₁.hom)).natTrans ≫
        Functor.whiskerLeft Lh (iU₁ ≪≫ cT₁.symm ≪≫ NatIso.hcomp iV₁ iW₁).inv := by
  ext X
  have hX := congr_app h X
  simp only [TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj] at hX
  simp only [TwoSquare.hComp, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    NatIso.hcomp_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.map_comp, Category.assoc, NatTrans.hcomp_app]
  dsimp only [TwoSquare.natTrans] at hX
  simp only [Category.assoc] at hX
  rw [← Functor.map_comp_assoc W₁ (SV.app X), ← iW₁.hom.naturality_assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc W₁T, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rw [← reassoc_of% hX]
  simp [← Functor.map_comp_assoc]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism (Profinite.padicAlgClRingObj ℓ) ℓ k

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Over (Spec (.of k))}
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
  [LocallyOfFiniteType Y₃.hom] [QuasiCompact Y₃.hom] [IsSeparated Y₃.hom]
  {h : X₁ ⟶ X₂} {v₁ : X₁ ⟶ Y₁} {v₂ : X₂ ⟶ Y₂} {k : Y₁ ⟶ Y₂} {w₁ : Y₁ ⟶ X₃} {w₂ : Y₂ ⟶ Y₃}
  {l : X₃ ⟶ Y₃}

section Triangles

variable (sq₁ : IsPullback h v₁ v₂ k) (sq₂ : IsPullback k w₁ w₂ l)

/-- The triangle of compactifications defining the composition isomorphism of `(v₂, w₂)`. -/
noncomputable abbrev pasteVertTriangle :
    AlgebraicGeometry.Compactification.Triangle v₂.left w₂.left :=
  triangleOfCompactifications (compactificationOverField v₂) (compactificationOverField w₂) _
    (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField v₂) (compactificationOverField w₂)).choose_spec

/-- The base change of `pasteVertTriangle` along the squares `sq₁` and `sq₂`. -/
noncomputable abbrev pasteVertTriangle' :
    AlgebraicGeometry.Compactification.Triangle v₁.left w₁.left :=
  (pasteVertTriangle (v₂ := v₂) (w₂ := w₂)).ofIsPullback sq₁.overLeft sq₂.overLeft
    (sq₁.paste_vert sq₂).overLeft


lemma isPullback_pasteVertTriangle_q :
    IsPullback ((compactificationOverField v₂).overBaseChangeFst sq₁)
      (Compactification.Triangle.overQ (pasteVertTriangle' sq₁ sq₂))
      (Compactification.Triangle.overQ (pasteVertTriangle (v₂ := v₂) (w₂ := w₂)))
      ((Compactification.Triangle.overCfg (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChangeFst
        (sq₁.paste_vert sq₂)) :=
  IsPullback.of_map (Over.forget _)
    (Over.OverMorphism.ext ((pasteVertTriangle (v₂ := v₂) (w₂ := w₂)).isPullback_baseChangeQ
      sq₂.overLeft).w)
    ((pasteVertTriangle (v₂ := v₂) (w₂ := w₂)).isPullback_baseChangeQ sq₂.overLeft)

lemma overBaseChangeFst_overP :
    (Compactification.Triangle.overCfg (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChangeFst
        (sq₁.paste_vert sq₂) ≫ Compactification.Triangle.overP (pasteVertTriangle (v₂ := v₂) (w₂ := w₂)) =
      Compactification.Triangle.overP (pasteVertTriangle' sq₁ sq₂) ≫
        (compactificationOverField w₂).overBaseChangeFst sq₂ :=
  Over.OverMorphism.ext (pasteVertTriangle (v₂ := v₂) (w₂ := w₂)).baseChangeP_fst.symm

/-- The compact-support exchange maps of the triangle `pasteVertTriangle` and its base change
are compatible with the composition isomorphisms of the triangles. -/
lemma pasteVert_compIso_shriekBaseChange :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))
    haveI := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
    Functor.whiskerRight
        ((𝔽).compIso (triangleShriekTriangle (pasteVertTriangle (v₂ := v₂) (w₂ := w₂)))).hom
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ l) ≫
      boundedConstructibleLowerShriekOfCompactificationBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ
        (Compactification.Triangle.overCfg (pasteVertTriangle (v₂ := v₂) (w₂ := w₂)))
        ((Compactification.Triangle.overCfg (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).ofIsPullback
          (sq₁.paste_vert sq₂).overLeft)
        ((Compactification.Triangle.overCfg (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChangeFst
          (sq₁.paste_vert sq₂))
        ((Compactification.Triangle.overCfg (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChange_isPullback_i
          (sq₁.paste_vert sq₂))
        ((Compactification.Triangle.overCfg (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChange_isPullback_g
          (sq₁.paste_vert sq₂)) =
    (TwoSquare.hComp
        (boundedConstructibleLowerShriekOfCompactificationBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ
          (compactificationOverField v₂) ((compactificationOverField v₂).ofIsPullback sq₁.overLeft)
          ((compactificationOverField v₂).overBaseChangeFst sq₁)
          ((compactificationOverField v₂).overBaseChange_isPullback_i sq₁)
          ((compactificationOverField v₂).overBaseChange_isPullback_g sq₁))
        (boundedConstructibleLowerShriekOfCompactificationBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ
          (compactificationOverField w₂) ((compactificationOverField w₂).ofIsPullback sq₂.overLeft)
          ((compactificationOverField w₂).overBaseChangeFst sq₂)
          ((compactificationOverField w₂).overBaseChange_isPullback_i sq₂)
          ((compactificationOverField w₂).overBaseChange_isPullback_g sq₂))).natTrans ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h)
        ((𝔽).compIso (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂))).hom := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))
  have := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))
  have := isIso_baseChange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
  have := isIso_exchange_triangleShriekTriangle ℓ (pasteVertTriangle' sq₁ sq₂)
  have : IsIso ((𝔽).baseChange (SepFinType.homMk h)
      (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂)).i₁
      (triangleShriekTriangle (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).i₁
      (SepFinType.homMk ((compactificationOverField v₂).overBaseChangeFst sq₁))
      (SepFinType.homMk_comp_homMk
        ((compactificationOverField v₂).overBaseChange_isPullback_i sq₁).w)).natTrans :=
    isIso_baseChange_boundedConstructibleExchangeFormalism (Profinite.padicAlgClRingObj ℓ) ℓ
      ((compactificationOverField v₂).overBaseChange_isPullback_i sq₁)
  have : IsIso ((𝔽).baseChange (SepFinType.homMk k)
      (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂)).i₂
      (triangleShriekTriangle (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).i₂
      (SepFinType.homMk ((compactificationOverField w₂).overBaseChangeFst sq₂))
      (SepFinType.homMk_comp_homMk
        ((compactificationOverField w₂).overBaseChange_isPullback_i sq₂).w)).natTrans :=
    isIso_baseChange_boundedConstructibleExchangeFormalism (Profinite.padicAlgClRingObj ℓ) ℓ
      ((compactificationOverField w₂).overBaseChange_isPullback_i sq₂)
  have : IsIso ((𝔽).baseChange (SepFinType.homMk h)
      (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂)).i
      (triangleShriekTriangle (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).i
      (SepFinType.homMk ((Compactification.Triangle.overCfg
        (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChangeFst (sq₁.paste_vert sq₂)))
      (SepFinType.homMk_comp_homMk ((Compactification.Triangle.overCfg
        (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChange_isPullback_i
          (sq₁.paste_vert sq₂)).w)).natTrans :=
    isIso_baseChange_boundedConstructibleExchangeFormalism (Profinite.padicAlgClRingObj ℓ) ℓ
      ((Compactification.Triangle.overCfg (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChange_isPullback_i
        (sq₁.paste_vert sq₂))
  have : IsIso ((𝔽).baseChange
      (SepFinType.homMk ((compactificationOverField v₂).overBaseChangeFst sq₁))
      (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂)).q
      (triangleShriekTriangle (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).q
      (SepFinType.homMk ((Compactification.Triangle.overCfg
        (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChangeFst (sq₁.paste_vert sq₂)))
      (SepFinType.homMk_comp_homMk (isPullback_pasteVertTriangle_q sq₁ sq₂).w)).natTrans :=
    isIso_baseChange_boundedConstructibleExchangeFormalism (Profinite.padicAlgClRingObj ℓ) ℓ
      (isPullback_pasteVertTriangle_q sq₁ sq₂)
  unfold boundedConstructibleLowerShriekOfCompactificationBaseChange
  exact (𝔽).compIso_shriekBaseChange (triangleShriekTriangle (pasteVertTriangle (v₂ := v₂) (w₂ := w₂)))
    (triangleShriekTriangle (pasteVertTriangle' sq₁ sq₂))
    (SepFinType.homMk ((compactificationOverField v₂).overBaseChangeFst sq₁))
    (SepFinType.homMk ((compactificationOverField w₂).overBaseChangeFst sq₂))
    (SepFinType.homMk ((Compactification.Triangle.overCfg
      (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChangeFst (sq₁.paste_vert sq₂)))
    (SepFinType.homMk_comp_homMk
      ((compactificationOverField v₂).overBaseChange_isPullback_i sq₁).w)
    (SepFinType.homMk_comp_homMk
      ((compactificationOverField v₂).overBaseChange_isPullback_g sq₁).w)
    (SepFinType.homMk_comp_homMk
      ((compactificationOverField w₂).overBaseChange_isPullback_i sq₂).w)
    (SepFinType.homMk_comp_homMk
      ((compactificationOverField w₂).overBaseChange_isPullback_g sq₂).w)
    (SepFinType.homMk_comp_homMk ((Compactification.Triangle.overCfg
      (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChange_isPullback_i (sq₁.paste_vert sq₂)).w)
    (SepFinType.homMk_comp_homMk ((Compactification.Triangle.overCfg
      (pasteVertTriangle (v₂ := v₂) (w₂ := w₂))).overBaseChange_isPullback_g (sq₁.paste_vert sq₂)).w)
    (SepFinType.homMk_comp_homMk (isPullback_pasteVertTriangle_q sq₁ sq₂).w)
    (SepFinType.homMk_comp_homMk (overBaseChangeFst_overP sq₁ sq₂))
end Triangles

end AlgebraicGeometry.ProEtale.CondensedRing
