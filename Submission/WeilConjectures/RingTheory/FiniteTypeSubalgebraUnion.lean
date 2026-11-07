/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Algebras as unions of finite type subalgebras, and fraction fields as colimits

* `Algebra.directed_adjoin_finset_and_iSup_eq_top` (blueprint `lem-kun-algebra-union`): an
  `R`-algebra is the directed union of its finitely generated subalgebras.
* `Subalgebra.isColimitCocone`: a directed family of subalgebras covering the whole algebra
  is a filtered colimit in `CommRingCat`.
* `Subalgebra.localizationSubalgebra`: for a subalgebra `S` of a domain `B` and a nonzero
  `g ∈ S`, the copy of `S_g` inside `Frac B`.
* `Subalgebra.isFiltered_and_isColimit_localizationSubalgebras` (blueprint
  `lem-kun-colim-of-localizations`): `Frac B` is the filtered colimit of the `(B_i)_g`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Algebra

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]


end Algebra

namespace Subalgebra

variable {R : Type*} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The diagram in `CommRingCat` given by a set of subalgebras ordered by inclusion. -/
@[simps]
def diagram (D : Set (Subalgebra R A)) : D ⥤ CommRingCat.{u} where
  obj S := CommRingCat.of S.1
  map {S T} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom

/-- The cocone with vertex `A` over the diagram of a set of subalgebras. -/
@[simps]
def cocone (D : Set (Subalgebra R A)) : Cocone (diagram D) where
  pt := CommRingCat.of A
  ι := { app S := CommRingCat.ofHom S.1.val.toRingHom }

/-- A directed set of subalgebras ordered by inclusion is a filtered category. -/
theorem isFiltered_of_directedOn {D : Set (Subalgebra R A)} (hD : DirectedOn (· ≤ ·) D)
    (hne : D.Nonempty) : IsFiltered D := by
  have : IsDirectedOrder D := ⟨fun S T ↦ by
    obtain ⟨U, hU, hSU, hTU⟩ := hD S.1 S.2 T.1 T.2
    exact ⟨⟨U, hU⟩, hSU, hTU⟩⟩
  have : Nonempty D := hne.to_subtype
  infer_instance

/-- A directed set `D` of subalgebras of `A` whose union is `A` exhibits `A` as the filtered
colimit of the members of `D` in `CommRingCat`. -/
noncomputable def isColimitCocone {D : Set (Subalgebra R A)} (hD : DirectedOn (· ≤ ·) D)
    (hcov : ∀ x : A, ∃ S ∈ D, x ∈ S) : IsColimit (cocone D) := by
  have := isFiltered_of_directedOn hD (by obtain ⟨S, hS, -⟩ := hcov 0; exact ⟨S, hS⟩)
  have := reflectsColimit_of_reflectsIsomorphisms (diagram D) (forget CommRingCat.{u})
  refine isColimitOfReflects (forget CommRingCat.{u}) (Types.FilteredColimit.isColimitOf' _ _
    (fun x ↦ ?_) (fun i x y h ↦ ⟨i, 𝟙 i, ?_⟩))
  · obtain ⟨S, hS, hx⟩ := hcov x
    exact ⟨⟨S, hS⟩, ⟨x, hx⟩, rfl⟩
  · exact Subtype.ext h

section Localization

variable {K : Type*} {B : Type u} [CommRing K] [CommRing B] [IsDomain B] [Algebra K B]

theorem isUnit_algebraMap_fractionRing_powers (S : Subalgebra K B) {g : S} (hg : g ≠ 0)
    (y : Submonoid.powers g) :
    IsUnit (((IsScalarTower.toAlgHom K B (FractionRing B)).comp S.val) y) := by
  obtain ⟨_, n, rfl⟩ := y
  refine IsUnit.mk0 _ ?_
  have hg' : (g : B) ≠ 0 := by simpa using hg
  simp [hg']

/-- For a subalgebra `S` of a domain `B` and a nonzero `g ∈ S`, the `K`-algebra map
`S_g → Frac B`. -/
noncomputable def awayToFractionRing (S : Subalgebra K B) {g : S} (hg : g ≠ 0) :
    Localization.Away g →ₐ[K] FractionRing B :=
  IsLocalization.liftAlgHom (isUnit_algebraMap_fractionRing_powers S hg)


/-- `S_g → Frac B` is compatible with the inclusion `S ⊆ B ⊆ Frac B`. -/
@[simp]
theorem awayToFractionRing_algebraMap (S : Subalgebra K B) {g : S} (hg : g ≠ 0) (a : S) :
    awayToFractionRing S hg (algebraMap S (Localization.Away g) a) =
      algebraMap B (FractionRing B) a := by
  rw [awayToFractionRing, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
  rfl

theorem awayToFractionRing_injective (S : Subalgebra K B) {g : S} (hg : g ≠ 0) :
    Function.Injective (awayToFractionRing S hg) := by
  rw [awayToFractionRing, IsLocalization.coe_liftAlgHom, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (Localization.Away g)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)).eq_iff]
  simp [(IsFractionRing.injective B (FractionRing B)).eq_iff]

/-- The copy of `S_g` inside `Frac B`, for a subalgebra `S` of a domain `B` and a nonzero
`g ∈ S`: the image of `awayToFractionRing`. -/
noncomputable def localizationSubalgebra (S : Subalgebra K B) {g : S} (hg : g ≠ 0) :
    Subalgebra K (FractionRing B) :=
  (awayToFractionRing S hg).range

/-- `localizationSubalgebra S hg` is isomorphic to `S_g`. -/
noncomputable def localizationSubalgebraEquiv (S : Subalgebra K B) {g : S} (hg : g ≠ 0) :
    Localization.Away g ≃ₐ[K] localizationSubalgebra S hg :=
  AlgEquiv.ofInjective _ (awayToFractionRing_injective S hg)


/-- The set of subalgebras `(B_i)_g ⊆ Frac B`, for `B_i` in a set `F` of subalgebras of `B` and
`g ∈ B_i` nonzero. -/
def localizationSubalgebras (F : Set (Subalgebra K B)) : Set (Subalgebra K (FractionRing B)) :=
  {T | ∃ S ∈ F, ∃ (g : S) (hg : g ≠ 0), T = localizationSubalgebra S hg}


end Localization

end Subalgebra

end
