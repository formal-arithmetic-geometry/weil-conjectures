/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization
public import WeilConjectures.CategoryTheory.Idempotents.TStructure

/-!
# The t-structure of a rationalization

Let `C` be an `R`-linear triangulated category, `M` a submonoid of `R` and
`Q : C ⥤ C[M⁻¹]` the rationalization (`CategoryTheory.Rationalization`), the Verdier quotient
of `C` by its `M`-torsion objects. A t-structure `t` on `C` induces a t-structure on `C[M⁻¹]`
(`CategoryTheory.Triangulated.TStructure.rationalization`): an object is `≤ n` (resp. `≥ n`) if
it is isomorphic to the image of an object of `C` which is `≤ n` (resp. `≥ n`) for `t`.

The orthogonality comes from the description of the morphisms of `C[M⁻¹]`: for every morphism
`f : Q X ⟶ Q Y` there are `m ∈ M` and `g : X ⟶ Y` with `m • f = Q g`
(`CategoryTheory.Rationalization.exists_smul_eq_map`). The truncation triangles are the images
under `Q` of those of `t`. The functor `Q` is t-exact, the induced t-structure is bounded when
`t` is, and its heart is the essential image of the heart of `t`.

## Main definitions

- `CategoryTheory.Triangulated.TStructure.rationalization`: the induced t-structure.

## Main results

- `CategoryTheory.Rationalization.exists_smul_eq_map`: morphisms of `C[M⁻¹]` are fractions
  `Q g / m`.
- `CategoryTheory.Triangulated.TStructure.rationalization_heart_iff`: the heart is the
  essential image of the heart of `t`.
- `CategoryTheory.Triangulated.TStructure.rationalization_bounded`: boundedness is inherited.
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits Pretriangulated ZeroObject

namespace CategoryTheory

variable {R : Type w} [CommRing R] {M : Submonoid R} {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]

namespace Rationalization

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] [IsTriangulated C] in
/-- If `s : Y ⟶ Y'` has `M`-torsion mapping cone, then some `m ∈ M` makes `m • 𝟙 Y'` factor
through `s`. -/
lemma exists_smul_id_eq_comp {Y Y' : C} {s : Y ⟶ Y'} (hs : W M C s) :
    ∃ m ∈ M, ∃ r : Y' ⟶ Y, m • 𝟙 Y' = r ≫ s := by
  obtain ⟨Z, g, h, hT, m, hm, hZ⟩ := hs
  obtain ⟨r, hr⟩ := Triangle.coyoneda_exact₂ _ hT (m • 𝟙 Y') (by
    change (m • 𝟙 Y') ≫ g = 0
    rw [Linear.smul_comp, id_comp, ← comp_id g, ← Linear.comp_smul, hZ, comp_zero])
  exact ⟨m, hm, r, hr⟩

variable (M C) in
/-- Every morphism `f : Q X ⟶ Q Y` of the rationalization is a fraction: `m • f = Q g` for
some `m ∈ M` and some morphism `g : X ⟶ Y` of `C`. -/
lemma exists_smul_eq_map {X Y : C} (f : (Q M C).obj X ⟶ (Q M C).obj Y) :
    ∃ m ∈ M, ∃ g : X ⟶ Y, m • f = (Q M C).map g := by
  obtain ⟨φ, rfl⟩ := Localization.exists_leftFraction (Q M C) (W M C) f
  obtain ⟨m, hm, r, hr⟩ := exists_smul_id_eq_comp φ.hs
  have : IsIso ((Q M C).map φ.s) := Localization.inverts (Q M C) (W M C) _ φ.hs
  refine ⟨m, hm, φ.f ≫ r, ?_⟩
  rw [Functor.map_comp, ← cancel_mono ((Q M C).map φ.s), assoc, ← Functor.map_comp, ← hr,
    Functor.map_smul, Functor.map_id, Linear.smul_comp, MorphismProperty.LeftFraction.map,
    assoc, IsIso.inv_hom_id, comp_id, Linear.comp_smul, comp_id]

/-- A morphism `Q X ⟶ Q Y` vanishes as soon as all morphisms `X ⟶ Y` of `C` vanish. -/
lemma eq_zero_of_subsingleton {X Y : C} (h : ∀ g : X ⟶ Y, g = 0)
    (f : (Q M C).obj X ⟶ (Q M C).obj Y) : f = 0 := by
  obtain ⟨m, hm, g, hg⟩ := exists_smul_eq_map M C f
  have : IsIso (m • 𝟙 ((Q M C).obj X)) := isIso_smul_id hm _
  rw [h g, Functor.map_zero, ← id_comp f, ← Linear.smul_comp] at hg
  exact (cancel_epi (m • 𝟙 ((Q M C).obj X))).1 (hg.trans (comp_zero).symm)

end Rationalization

namespace Triangulated.TStructure

open Rationalization

variable (t : TStructure C)

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/-- The t-structure induced by a t-structure `t` of `C` on its rationalization `C[M⁻¹]`: the
objects `≤ n` (resp. `≥ n`) are those isomorphic to `Q X` with `X` in `C` which is `≤ n`
(resp. `≥ n`) for `t`. -/
noncomputable def rationalization : TStructure (Rationalization M C) where
  le n := (t.le n).map (Q M C)
  ge n := (t.ge n).map (Q M C)
  le_shift n a n' h X := by
    rintro ⟨A, hA, ⟨e⟩⟩
    exact ⟨A⟦a⟧, t.le_shift n a n' h A hA,
      ⟨((Q M C).commShiftIso a).app A ≪≫ (shiftFunctor _ a).mapIso e⟩⟩
  ge_shift n a n' h X := by
    rintro ⟨A, hA, ⟨e⟩⟩
    exact ⟨A⟦a⟧, t.ge_shift n a n' h A hA,
      ⟨((Q M C).commShiftIso a).app A ≪≫ (shiftFunctor _ a).mapIso e⟩⟩
  zero' {X Y} f := by
    rintro ⟨A, hA, ⟨e⟩⟩ ⟨B, hB, ⟨e'⟩⟩
    have h := eq_zero_of_subsingleton (fun g ↦ t.zero' g hA hB) (e.hom ≫ f ≫ e'.inv)
    simpa using congr(e.inv ≫ $h ≫ e'.hom)
  le_zero_le := by
    rintro X ⟨A, hA, e⟩
    exact ⟨A, t.le_zero_le _ hA, e⟩
  ge_one_le := by
    rintro X ⟨A, hA, e⟩
    exact ⟨A, t.ge_one_le _ hA, e⟩
  exists_triangle_zero_one X := by
    let e := (Q M C).objObjPreimageIso X
    obtain ⟨A, B, hA, hB, f, g, h, hT⟩ := t.exists_triangle_zero_one ((Q M C).objPreimage X)
    refine ⟨(Q M C).obj A, (Q M C).obj B, (t.le 0).prop_map_obj _ hA,
      (t.ge 1).prop_map_obj _ hB, (Q M C).map f ≫ e.hom, e.inv ≫ (Q M C).map g,
      (Q M C).map h ≫ ((Q M C).commShiftIso (1 : ℤ)).hom.app A, ?_⟩
    refine isomorphic_distinguished _ ((Q M C).map_distinguished _ hT) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) (by simp; rfl) (by simp; rfl)
      (by simp; rfl)

variable {t}

lemma rationalization_le_iff (n : ℤ) (X : Rationalization M C) :
    (t.rationalization M).le n X ↔ ∃ A, t.le n A ∧ Nonempty ((Q M C).obj A ≅ X) :=
  Iff.rfl

lemma rationalization_ge_iff (n : ℤ) (X : Rationalization M C) :
    (t.rationalization M).ge n X ↔ ∃ A, t.ge n A ∧ Nonempty ((Q M C).obj A ≅ X) :=
  Iff.rfl

/-- The rationalization functor `Q` is right t-exact: it carries objects `≤ n` to objects
`≤ n`. -/
instance isLE_rationalization_obj (A : C) (n : ℤ) [t.IsLE A n] :
    (t.rationalization M).IsLE ((Q M C).obj A) n :=
  ⟨(t.le n).prop_map_obj _ (t.le_of_isLE A n)⟩

/-- The rationalization functor `Q` is left t-exact: it carries objects `≥ n` to objects
`≥ n`. -/
instance isGE_rationalization_obj (A : C) (n : ℤ) [t.IsGE A n] :
    (t.rationalization M).IsGE ((Q M C).obj A) n :=
  ⟨(t.ge n).prop_map_obj _ (t.ge_of_isGE A n)⟩

/-- Boundedness passes to the rationalization. -/
lemma rationalization_bounded (ht : ∀ X : C, t.bounded X) (X : Rationalization M C) :
    (t.rationalization M).bounded X := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ht ((Q M C).objPreimage X)
  exact ⟨⟨a, ⟨⟨_, ha.1, ⟨(Q M C).objObjPreimageIso X⟩⟩⟩⟩,
    ⟨b, ⟨⟨_, hb.1, ⟨(Q M C).objObjPreimageIso X⟩⟩⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The heart of the induced t-structure on the rationalization is the essential image of the
heart of `t`. -/
lemma rationalization_heart_iff (X : Rationalization M C) :
    (t.rationalization M).heart X ↔ ∃ A, t.heart A ∧ Nonempty ((Q M C).obj A ≅ X) := by
  constructor
  · rintro ⟨⟨A, hA, ⟨e⟩⟩, hX⟩
    have : t.IsLE A 0 := ⟨hA⟩
    have : (t.rationalization M).IsGE ((Q M C).obj A) 0 :=
      ⟨((t.rationalization M).ge 0).prop_of_iso e.symm hX⟩
    obtain ⟨e', -⟩ := (t.rationalization M).triangle_iso_exists
      ((Q M C).map_distinguished _ (t.triangleLEGE_distinguished (-1) 0 (by lia) A))
      (contractible_distinguished₁ ((Q M C).obj A)) (Iso.refl _) (-1) 0
      (isLE_rationalization_obj ((t.truncLE (-1)).obj A) (-1))
      (isGE_rationalization_obj ((t.truncGE 0).obj A) 0)
      ((t.rationalization M).isLE_of_isZero (isZero_zero _) (-1)) this
    exact ⟨(t.truncGE 0).obj A, ⟨t.le_of_isLE _ 0, t.ge_of_isGE _ 0⟩,
      ⟨Triangle.π₃.mapIso e' ≪≫ e⟩⟩
  · rintro ⟨A, ⟨hA, hA'⟩, ⟨e⟩⟩
    exact ⟨⟨A, hA, ⟨e⟩⟩, ⟨A, hA', ⟨e⟩⟩⟩


/-- If `C` carries a bounded t-structure, its rationalization `C[M⁻¹]` is idempotent complete:
the induced t-structure is bounded. This is the formal part of blueprint
`thm-weil-pbc-finite-stage-karoubian`. -/
theorem isIdempotentComplete_rationalization (ht : ∀ X : C, t.bounded X) :
    IsIdempotentComplete (Rationalization M C) :=
  (t.rationalization M).isIdempotentComplete_of_bounded (rationalization_bounded ht)

/-- If `C` carries a bounded t-structure, the canonical functor from its rationalization
`C[M⁻¹]` to the Karoubi envelope of `C[M⁻¹]` is an equivalence of triangulated categories. -/
theorem isEquivalence_toKaroubi_rationalization (ht : ∀ X : C, t.bounded X) :
    (Idempotents.toKaroubi (Rationalization M C)).IsEquivalence ∧
      (Idempotents.toKaroubi (Rationalization M C)).IsTriangulated :=
  (t.rationalization M).isEquivalence_toKaroubi_and_isTriangulated_of_bounded
    (rationalization_bounded ht)

end Triangulated.TStructure

end CategoryTheory
