/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateTransport

/-!
# Transport of open base change and clopen projections

Comparison functors compatible with inverse images carry the unit-transpose open base-change
comparison, the open-to-direct-image comparison and the clopen projection to their
counterparts, the open extensions being compared by the mates of the inverse-image
comparisons.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section

open CategoryTheory Functor

namespace CategoryTheory.ProperOpenTransport

section BetaInv

variable {U U' X X' : Type*} [Category U] [Category U'] [Category X] [Category X']
  {U₁ U₁' X₁ X₁' : Type*} [Category U₁] [Category U₁'] [Category X₁] [Category X₁']

/-- The open base-change comparison, as the transpose of the pulled-back open unit. -/
def betaInvApp {PgU : U ⥤ U'} {Jj : U ⥤ X} {Pj : X ⥤ U} (adjJ : Jj ⊣ Pj)
    {Jj' : U' ⥤ X'} {Pj' : X' ⥤ U'} (adjJ' : Jj' ⊣ Pj') {Pg : X ⥤ X'}
    (sq : Pg ⋙ Pj' ≅ Pj ⋙ PgU) (M : U) :
    Jj'.obj (PgU.obj M) ⟶ Pg.obj (Jj.obj M) :=
  (adjJ'.homEquiv _ _).symm (PgU.map (adjJ.unit.app M) ≫ sq.inv.app (Jj.obj M))

theorem unit_comp_map_betaInvApp {PgU : U ⥤ U'} {Jj : U ⥤ X} {Pj : X ⥤ U} (adjJ : Jj ⊣ Pj)
    {Jj' : U' ⥤ X'} {Pj' : X' ⥤ U'} (adjJ' : Jj' ⊣ Pj') {Pg : X ⥤ X'}
    (sq : Pg ⋙ Pj' ≅ Pj ⋙ PgU) (M : U) :
    adjJ'.unit.app (PgU.obj M) ≫ Pj'.map (betaInvApp adjJ adjJ' sq M) =
      PgU.map (adjJ.unit.app M) ≫ sq.inv.app (Jj.obj M) := by
  have := (adjJ'.homEquiv _ _).apply_symm_apply
    (PgU.map (adjJ.unit.app M) ≫ sq.inv.app (Jj.obj M))
  rwa [Adjunction.homEquiv_unit] at this

/-- The open extension comparison: the left mate of an inverse-image comparison. -/
abbrev openComparison {Jj : U ⥤ X} {Pj : X ⥤ U} (adjJ : Jj ⊣ Pj)
    {Jj₁ : U₁ ⥤ X₁} {Pj₁ : X₁ ⥤ U₁} (adjJ₁ : Jj₁ ⊣ Pj₁) {ΦU : U ⥤ U₁} {ΦX : X ⥤ X₁}
    (φ : Pj ⋙ ΦU ≅ ΦX ⋙ Pj₁) : ΦU ⋙ Jj₁ ⟶ Jj ⋙ ΦX :=
  (mateEquiv adjJ adjJ₁).symm φ.hom

theorem unit_openComparison {Jj : U ⥤ X} {Pj : X ⥤ U} (adjJ : Jj ⊣ Pj)
    {Jj₁ : U₁ ⥤ X₁} {Pj₁ : X₁ ⥤ U₁} (adjJ₁ : Jj₁ ⊣ Pj₁) {ΦU : U ⥤ U₁} {ΦX : X ⥤ X₁}
    (φ : Pj ⋙ ΦU ≅ ΦX ⋙ Pj₁) (M : U) :
    ΦU.map (adjJ.unit.app M) ≫ φ.hom.app (Jj.obj M) =
      adjJ₁.unit.app (ΦU.obj M) ≫ Pj₁.map ((openComparison adjJ adjJ₁ φ).app M) :=
  unit_mateEquiv_symm adjJ adjJ₁ φ.hom M

/-- The open base-change comparison is transported along comparisons compatible with the
inverse images of the square. -/
theorem betaInvApp_transport {PgU : U ⥤ U'} {Jj : U ⥤ X} {Pj : X ⥤ U} (adjJ : Jj ⊣ Pj)
    {Jj' : U' ⥤ X'} {Pj' : X' ⥤ U'} (adjJ' : Jj' ⊣ Pj') {Pg : X ⥤ X'}
    (sq : Pg ⋙ Pj' ≅ Pj ⋙ PgU)
    {PgU₁ : U₁ ⥤ U₁'} {Jj₁ : U₁ ⥤ X₁} {Pj₁ : X₁ ⥤ U₁} (adjJ₁ : Jj₁ ⊣ Pj₁)
    {Jj₁' : U₁' ⥤ X₁'} {Pj₁' : X₁' ⥤ U₁'} (adjJ₁' : Jj₁' ⊣ Pj₁') {Pg₁ : X₁ ⥤ X₁'}
    (sq₁ : Pg₁ ⋙ Pj₁' ≅ Pj₁ ⋙ PgU₁)
    {ΦU : U ⥤ U₁} {ΦU' : U' ⥤ U₁'} {ΦX : X ⥤ X₁} {ΦX' : X' ⥤ X₁'}
    (φgU : PgU ⋙ ΦU' ≅ ΦU ⋙ PgU₁) (φj : Pj ⋙ ΦU ≅ ΦX ⋙ Pj₁)
    (φj' : Pj' ⋙ ΦU' ≅ ΦX' ⋙ Pj₁') (φg : Pg ⋙ ΦX' ≅ ΦX ⋙ Pg₁)
    (hsq : ∀ x : X, ΦU'.map (sq.inv.app x) ≫ φj'.hom.app (Pg.obj x) ≫
        Pj₁'.map (φg.hom.app x) =
      φgU.hom.app (Pj.obj x) ≫ PgU₁.map (φj.hom.app x) ≫ sq₁.inv.app (ΦX.obj x))
    (M : U) :
    (openComparison adjJ' adjJ₁' φj').app (PgU.obj M) ≫
        ΦX'.map (betaInvApp adjJ adjJ' sq M) ≫ φg.hom.app (Jj.obj M) =
      Jj₁'.map (φgU.hom.app M) ≫ betaInvApp adjJ₁ adjJ₁' sq₁ (ΦU.obj M) ≫
        Pg₁.map ((openComparison adjJ adjJ₁ φj).app M) := by
  have hb := unit_comp_map_betaInvApp adjJ adjJ' sq M
  have hb₁ := unit_comp_map_betaInvApp adjJ₁ adjJ₁' sq₁ (ΦU.obj M)
  have n1 := φj'.hom.naturality (betaInvApp adjJ adjJ' sq M)
  have n2 := φgU.hom.naturality (adjJ.unit.app M)
  have n3 := adjJ₁'.unit.naturality (φgU.hom.app M)
  have n4 := sq₁.inv.naturality ((openComparison adjJ adjJ₁ φj).app M)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n1 n2 n3 n4
  apply (adjJ₁'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [← Category.assoc (adjJ₁'.unit.app _), ← unit_openComparison adjJ' adjJ₁' φj' (PgU.obj M)]
  simp only [Category.assoc]
  rw [← reassoc_of% n1, ← ΦU'.map_comp_assoc, hb, ΦU'.map_comp, Category.assoc, hsq,
    reassoc_of% n2]
  rw [← Category.assoc (adjJ₁'.unit.app _), ← n3]
  simp only [Category.assoc]
  rw [← Category.assoc (adjJ₁'.unit.app _), hb₁]
  simp only [Category.assoc]
  rw [← n4]
  rw [← PgU₁.map_comp_assoc, ← PgU₁.map_comp_assoc, unit_openComparison]

end BetaInv

section OpenToPush

variable {U X U₁ X₁ : Type*} [Category U] [Category X] [Category U₁] [Category X₁]
  {J : U ⥤ X} {P : X ⥤ U} {R : U ⥤ X} (adjJ : J ⊣ P) (adjP : P ⊣ R) [IsIso adjJ.unit]
  {J₁ : U₁ ⥤ X₁} {P₁ : X₁ ⥤ U₁} {R₁ : U₁ ⥤ X₁} (adjJ₁ : J₁ ⊣ P₁) (adjP₁ : P₁ ⊣ R₁)
  [IsIso adjJ₁.unit]

/-- The comparison from open extension to direct image, fixed by the two units. -/
def openToPush : J ⟶ R where
  app M := adjP.unit.app (J.obj M) ≫ R.map ((inv adjJ.unit).app M)
  naturality M N f := by
    have h₁ := adjP.unit.naturality (J.map f)
    have h₂ := (inv adjJ.unit).naturality f
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂ ⊢
    rw [reassoc_of% h₁, ← R.map_comp, h₂, R.map_comp, Category.assoc]

/-- The clopen projection: the direct-image unit followed by the inverse comparison. -/
def clopenProjection [IsIso (openToPush adjJ adjP)] : 𝟭 X ⟶ P ⋙ J :=
  adjP.unit ≫ Functor.whiskerLeft P (inv (openToPush adjJ adjP))

variable {ΦU : U ⥤ U₁} {ΦX : X ⥤ X₁} (φ : P ⋙ ΦU ≅ ΦX ⋙ P₁)

/-- The open-to-direct-image comparison is transported along a comparison of inverse images,
open extensions and direct images being compared by its mates. -/
theorem openToPush_transport (M : U) :
    (openComparison adjJ adjJ₁ φ).app M ≫ ΦX.map ((openToPush adjJ adjP).app M) ≫
        (mateEquiv adjP adjP₁ φ.inv).app M =
      (openToPush adjJ₁ adjP₁).app (ΦU.obj M) := by
  have hu := map_unit_comp_mateEquiv_app adjP adjP₁ φ (J.obj M)
  have hn := (mateEquiv adjP adjP₁ φ.inv).naturality ((inv adjJ.unit).app M)
  have hn' := adjP₁.unit.naturality ((openComparison adjJ adjJ₁ φ).app M)
  have hc : P₁.map ((openComparison adjJ adjJ₁ φ).app M) ≫ φ.inv.app (J.obj M) ≫
      ΦU.map ((inv adjJ.unit).app M) = (inv adjJ₁.unit).app (ΦU.obj M) := by
    rw [← cancel_epi (adjJ₁.unit.app (ΦU.obj M)), ← Category.assoc,
      ← unit_openComparison adjJ adjJ₁ φ M]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← ΦU.map_comp]
    simp
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hn hn'
  simp only [openToPush, Functor.map_comp, Category.assoc]
  erw [hn, reassoc_of% hu, reassoc_of% hn']
  rw [← R₁.map_comp, ← R₁.map_comp, ← hc]

/-- The clopen projection is transported along a comparison of inverse images. -/
theorem clopenProjection_transport [IsIso (openToPush adjJ adjP)]
    [IsIso (openToPush adjJ₁ adjP₁)] [IsIso (openComparison adjJ adjJ₁ φ)] (M : X) :
    ΦX.map ((clopenProjection adjJ adjP).app M) =
      (clopenProjection adjJ₁ adjP₁).app (ΦX.obj M) ≫ J₁.map (φ.inv.app M) ≫
        (openComparison adjJ adjJ₁ φ).app (P.obj M) := by
  have ht := openToPush_transport adjJ adjP adjJ₁ adjP₁ φ (P.obj M)
  have hu := map_unit_comp_mateEquiv_app adjP adjP₁ φ M
  have hn := (openToPush adjJ₁ adjP₁).naturality (φ.inv.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hn
  have : IsIso (ΦX.map ((openToPush adjJ adjP).app (P.obj M)) ≫
      (mateEquiv adjP adjP₁ φ.inv).app (P.obj M)) := by
    have : IsIso ((openComparison adjJ adjJ₁ φ).app (P.obj M) ≫
        ΦX.map ((openToPush adjJ adjP).app (P.obj M)) ≫
          (mateEquiv adjP adjP₁ φ.inv).app (P.obj M)) := by
      rw [ht]; infer_instance
    exact IsIso.of_isIso_comp_left ((openComparison adjJ adjJ₁ φ).app (P.obj M)) _
  rw [← cancel_mono (ΦX.map ((openToPush adjJ adjP).app (P.obj M)) ≫
    (mateEquiv adjP adjP₁ φ.inv).app (P.obj M))]
  simp only [Category.assoc]
  erw [ht]
  simp only [clopenProjection, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc, NatIso.isIso_inv_app, ← ΦX.map_comp_assoc, IsIso.inv_hom_id,
    Functor.map_id, Category.id_comp]
  erw [hu, hn, IsIso.inv_hom_id_assoc]

end OpenToPush

end CategoryTheory.ProperOpenTransport
