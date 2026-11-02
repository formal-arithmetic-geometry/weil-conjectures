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

@[expose] public section

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

end CategoryTheory.ProperOpenTransport
