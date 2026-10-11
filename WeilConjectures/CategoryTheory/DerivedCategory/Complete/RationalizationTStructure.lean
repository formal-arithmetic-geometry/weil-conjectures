/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationMap
public import WeilConjectures.CategoryTheory.Idempotents.TStructure

/-!
# The t-structure on a rationalization

Let `M` be a submonoid of a commutative ring `R`, let `C` be an `R`-linear triangulated category
with `R`-linear shift functors, and let `Q : C ⥤ Rationalization M C` be the rationalization of
`C` at `M` (`CategoryTheory.Rationalization`). A t-structure `t` on `C` induces a t-structure
`t.rationalization M` on `Rationalization M C` (blueprint `prop-weil-localized-tstructure`): an
object is `≤ n` (resp. `≥ n`) if it is isomorphic to the image under `Q` of an object which is
`≤ n` (resp. `≥ n`) for `t`.

The truncation triangles are the images under `Q` of those of `t`. The orthogonality holds
because the `Hom` groups of the rationalization are those of `C` with the elements of `M`
inverted: a morphism `Q X ⟶ Q Y` becomes the image of a morphism `X ⟶ Y` after multiplication by
some `m ∈ M` (`CategoryTheory.Rationalization.exists_smul_eq_map`), and multiplication by `m`
is injective in the rationalization (`CategoryTheory.Rationalization.smul_left_injective`).

The functor `Q` is t-exact, the induced t-structure is bounded if `t` is, and its heart is the
essential image of the heart of `t`. In particular, when `t` is bounded, the rationalization is
idempotent complete and its canonical functor into its Karoubi envelope is an exact equivalence
(blueprint `thm-weil-pbc-finite-stage-karoubian`), by
`CategoryTheory.Triangulated.TStructure.isIdempotentComplete_of_bounded`.

In the blueprint, `C` is the integral category `D^b_c(T, 𝒪_E)` with its standard t-structure
(`prop-weil-pbc-integral-tstructure`), `M` consists of the powers of a uniformizer (or all
nonzero elements of `𝒪_E`), and the rationalization is the rational category `D^b_c(T, E)`.

## Main definitions and results

- `CategoryTheory.Triangulated.TStructure.rationalization`: the induced t-structure.
- `CategoryTheory.Triangulated.TStructure.bounded_rationalization`: it is bounded if `t` is.
- `CategoryTheory.Triangulated.TStructure.heart_rationalization`: its heart.
- `CategoryTheory.Triangulated.TStructure.isIdempotentComplete_rationalization`: the
  rationalization of a triangulated category with a bounded t-structure is idempotent complete.
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Triangulated.TStructure

variable {R : Type w} [CommRing R] (M : Submonoid R)
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C] (t : TStructure C)

open Rationalization

/-- Blueprint `prop-weil-localized-tstructure`: a t-structure `t` on an `R`-linear triangulated
category `C` induces a t-structure on its rationalization at a submonoid `M` of `R`, whose
objects `≤ n` (resp. `≥ n`) are those isomorphic to the image of an object `≤ n` (resp. `≥ n`)
for `t`. Its truncation triangles are the images of those of `t`. -/
noncomputable def rationalization : TStructure (Rationalization M C) where
  le n := (t.le n).map (Q M C)
  ge n := (t.ge n).map (Q M C)
  le_shift n a n' h Y := by
    rintro ⟨X, hX, ⟨e⟩⟩
    exact ⟨X⟦a⟧, t.le_shift n a n' h X hX,
      ⟨((Q M C).commShiftIso a).app X ≪≫ (shiftFunctor _ a).mapIso e⟩⟩
  ge_shift n a n' h Y := by
    rintro ⟨X, hX, ⟨e⟩⟩
    exact ⟨X⟦a⟧, t.ge_shift n a n' h X hX,
      ⟨((Q M C).commShiftIso a).app X ≪≫ (shiftFunctor _ a).mapIso e⟩⟩
  zero' Y Y' f := by
    rintro ⟨X, hX, ⟨e⟩⟩ ⟨X', hX', ⟨e'⟩⟩
    obtain ⟨m, hm, g, hg⟩ := exists_smul_eq_map (e.hom ≫ f ≫ e'.inv)
    rw [t.zero' g hX hX', Functor.map_zero] at hg
    have h0 : e.hom ≫ f ≫ e'.inv = 0 :=
      smul_left_injective hm (by simpa using hg)
    simpa using h0
  le_zero_le := ObjectProperty.map_monotone t.le_zero_le _
  ge_one_le := ObjectProperty.map_monotone t.ge_one_le _
  exists_triangle_zero_one A := by
    let e := (Q M C).objObjPreimageIso A
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := t.exists_triangle_zero_one ((Q M C).objPreimage A)
    refine ⟨_, _, ObjectProperty.prop_map_obj _ _ hX, ObjectProperty.prop_map_obj _ _ hY,
      (Q M C).map f ≫ e.hom, e.inv ≫ (Q M C).map g,
      (Q M C).map h ≫ ((Q M C).commShiftIso (1 : ℤ)).hom.app X, ?_⟩
    refine isomorphic_distinguished _ ((Q M C).map_distinguished _ hT) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) (by simp [Functor.mapTriangle])
      (by simp [Functor.mapTriangle]) (by
        simp [Functor.mapTriangle]
        rfl)

lemma rationalization_le (n : ℤ) : (t.rationalization M).le n = (t.le n).map (Q M C) := rfl

lemma rationalization_ge (n : ℤ) : (t.rationalization M).ge n = (t.ge n).map (Q M C) := rfl

/-- Blueprint `prop-weil-localized-tstructure`: the localization functor is t-exact; it
preserves the objects `≤ n`. -/
instance isLE_rationalization_obj (X : C) (n : ℤ) [t.IsLE X n] :
    (t.rationalization M).IsLE ((Q M C).obj X) n :=
  ⟨ObjectProperty.prop_map_obj _ _ (t.le_of_isLE X n)⟩

/-- Blueprint `prop-weil-localized-tstructure`: the localization functor is t-exact; it
preserves the objects `≥ n`. -/
instance isGE_rationalization_obj (X : C) (n : ℤ) [t.IsGE X n] :
    (t.rationalization M).IsGE ((Q M C).obj X) n :=
  ⟨ObjectProperty.prop_map_obj _ _ (t.ge_of_isGE X n)⟩

/-- Blueprint `prop-weil-localized-tstructure`: the t-structure on the rationalization is
bounded if `t` is, every object of the rationalization being the image of an object of `C`. -/
lemma bounded_rationalization (ht : ∀ X : C, t.bounded X) (Y : Rationalization M C) :
    (t.rationalization M).bounded Y := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ht ((Q M C).objPreimage Y)
  exact ⟨⟨a, (t.rationalization M).isGE_of_iso ((Q M C).objObjPreimageIso Y) a⟩,
    ⟨b, (t.rationalization M).isLE_of_iso ((Q M C).objObjPreimageIso Y) b⟩⟩

/-- Blueprint `prop-weil-localized-tstructure`: the heart of the t-structure on the
rationalization is the essential image of the heart of `t`. An object `Y ≅ Q A` of the heart
with `A ≤ 0` is isomorphic to `Q (τ_{≥ 0} A)`, because `Q (τ_{≤ -1} A) ≅ τ_{≤ -1} Y` vanishes. -/
lemma heart_rationalization : (t.rationalization M).heart = t.heart.map (Q M C) := by
  refine le_antisymm ?_ ?_
  · rintro Y ⟨⟨A, hA, ⟨e⟩⟩, hY⟩
    have : t.IsLE A 0 := ⟨hA⟩
    have : (t.rationalization M).IsGE ((Q M C).obj A) 0 :=
      ⟨((t.rationalization M).ge 0).prop_of_iso e.symm hY⟩
    obtain ⟨e', -⟩ := (t.rationalization M).triangle_iso_exists
      ((Q M C).map_distinguished _ (t.triangleLEGE_distinguished (-1) 0 (neg_add_cancel 1) A))
      ((t.rationalization M).triangleLEGE_distinguished (-1) 0 (neg_add_cancel 1) ((Q M C).obj A))
      (Iso.refl _) (-1) 0 (t.isLE_rationalization_obj M ((t.truncLE (-1)).obj A) (-1))
      (t.isGE_rationalization_obj M ((t.truncGE 0).obj A) 0)
      (inferInstanceAs ((t.rationalization M).IsLE
        (((t.rationalization M).truncLE (-1)).obj ((Q M C).obj A)) (-1)))
      (inferInstanceAs ((t.rationalization M).IsGE
        (((t.rationalization M).truncGE 0).obj ((Q M C).obj A)) 0))
    have hZ : IsZero ((Q M C).obj ((t.truncLE (-1)).obj A)) :=
      ((t.rationalization M).isZero_truncLE_obj_of_isGE (-1) 0 (neg_add_cancel 1) _).of_iso
        (Triangle.π₁.mapIso e')
    have : IsIso ((Q M C).map ((t.truncGEπ 0).app A)) := (Triangle.isZero₁_iff_isIso₂ _
      ((Q M C).map_distinguished _
        (t.triangleLEGE_distinguished (-1) 0 (neg_add_cancel 1) A))).1 hZ
    exact ⟨(t.truncGE 0).obj A, ⟨t.le_of_isLE _ 0, t.ge_of_isGE _ 0⟩,
      ⟨(asIso ((Q M C).map ((t.truncGEπ 0).app A))).symm ≪≫ e⟩⟩
  · rintro Y ⟨A, ⟨hA, hA'⟩, ⟨e⟩⟩
    exact ⟨⟨A, hA, ⟨e⟩⟩, ⟨A, hA', ⟨e⟩⟩⟩

/-- Blueprint `thm-weil-pbc-finite-stage-karoubian`: the rationalization of a triangulated
category with a bounded t-structure is idempotent complete, since it carries the induced bounded
t-structure (`prop-weil-localized-tstructure`) and triangulated categories with a bounded
t-structure are idempotent complete (`thm-weil-karoubian-bounded-t`). -/
theorem isIdempotentComplete_rationalization (ht : ∀ X : C, t.bounded X) :
    IsIdempotentComplete (Rationalization M C) :=
  (t.rationalization M).isIdempotentComplete_of_bounded (t.bounded_rationalization M ht)

/-- Blueprint `thm-weil-pbc-finite-stage-karoubian`: for a triangulated category with a bounded
t-structure, the canonical functor from its rationalization into the Karoubi envelope of the
rationalization is an exact equivalence. -/
theorem isEquivalence_toKaroubi_rationalization (ht : ∀ X : C, t.bounded X) :
    (Idempotents.toKaroubi (Rationalization M C)).IsEquivalence ∧
      (Idempotents.toKaroubi (Rationalization M C)).IsTriangulated :=
  (t.rationalization M).isEquivalence_toKaroubi_and_isTriangulated_of_bounded
    (t.bounded_rationalization M ht)

end CategoryTheory.Triangulated.TStructure
