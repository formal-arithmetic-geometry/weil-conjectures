/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions

/-!
# The agreement locus of two sections of an étale sheaf

For a sheaf `F` of modules on the small étale site of a scheme `Y`, an étale `Y`-scheme `T`
and two sections `a b ∈ F(T)`, the *agreement locus* is the set of points of `T` having an
étale neighbourhood on which `a` and `b` agree. It is open, it is compatible with restriction
along morphisms of étale `Y`-schemes, it is all of `T` exactly when `a = b`, and a point lies in
it exactly when the germs of `a` and `b` at a geometric point over it agree.

## Main definitions

- `AlgebraicGeometry.Etale.agreementLocus`: the agreement locus of two sections.

## Main statements

- `AlgebraicGeometry.Etale.isOpen_agreementLocus`: the agreement locus is open.
- `AlgebraicGeometry.Etale.eq_of_agreementLocus_eq_univ`: two sections agreeing everywhere
  locally are equal.
- `AlgebraicGeometry.Etale.mem_agreementLocus_map_iff`: the agreement locus of the restrictions
  along `g : T' ⟶ T` is the preimage of the agreement locus.
- `AlgebraicGeometry.Etale.mem_agreementLocus_iff_toPresheafFiber_eq`: a point lies in the
  agreement locus iff the germs at a geometric point over it agree.
- `AlgebraicGeometry.Etale.exists_eq_map_of_compatible`: gluing of sections along a jointly
  surjective family of étale morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
  (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- A morphism of étale `Y`-schemes is étale. -/
lemma etale_left {T T' : Y.Etale} (g : T' ⟶ T) : AlgebraicGeometry.Etale g.left :=
  MorphismProperty.of_postcomp @AlgebraicGeometry.Etale g.left T.hom T.prop
    (by rw [MorphismProperty.Over.w g]; exact T'.prop)

/-- The agreement locus of two sections `a b ∈ F(T)` of an étale sheaf: the points of `T` lying
in the image of an étale `T`-scheme on which `a` and `b` agree. -/
def agreementLocus {T : Y.Etale} (a b : F.obj.obj (op T)) : Set T.left :=
  {z | ∃ (U : Y.Etale) (f : U ⟶ T), z ∈ Set.range f.left ∧ F.obj.map f.op a = F.obj.map f.op b}

variable {F}

lemma range_subset_agreementLocus {T U : Y.Etale} {a b : F.obj.obj (op T)} (f : U ⟶ T)
    (h : F.obj.map f.op a = F.obj.map f.op b) :
    Set.range f.left ⊆ agreementLocus F a b :=
  fun _ hz ↦ ⟨U, f, hz, h⟩

/-- The agreement locus of two sections is open: it is a union of images of étale morphisms. -/
lemma isOpen_agreementLocus {T : Y.Etale} (a b : F.obj.obj (op T)) :
    IsOpen (agreementLocus F a b) := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨U, f, hz, h⟩
  have := etale_left f
  exact ⟨_, range_subset_agreementLocus f h, f.left.isOpenMap.isOpen_range, hz⟩

/-- The sheaf `F` composed with the forgetful functor is a sheaf of types. -/
lemma isSheaf_forget : Presieve.IsSheaf Y.smallEtaleTopology
    (F.obj ⋙ CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)).1 F.property)

/-- Sections of an étale sheaf which agree on the members of a jointly surjective family of
étale morphisms are equal. -/
lemma eq_of_forall_map_eq {T : Y.Etale} {ι : Type*} {U : ι → Y.Etale} (f : ∀ i, U i ⟶ T)
    (hf : ⋃ i, Set.range (f i).left = Set.univ) {a b : F.obj.obj (op T)}
    (h : ∀ i, F.obj.map (f i).op a = F.obj.map (f i).op b) : a = b := by
  have hmem := (ofArrows_mem_smallEtaleTopology_iff f).2 hf
  have hsep := (isSheaf_forget (F := F) _ hmem).isSeparatedFor
  rw [Sieve.ofArrows, ← Presieve.isSeparatedFor_iff_generate] at hsep
  refine hsep.ext fun V g hg ↦ ?_
  obtain ⟨i⟩ := hg
  exact h i

/-- Two sections whose agreement locus is everything are equal. -/
lemma eq_of_agreementLocus_eq_univ {T : Y.Etale} {a b : F.obj.obj (op T)}
    (h : agreementLocus F a b = Set.univ) : a = b := by
  have hz : ∀ z : T.left, z ∈ agreementLocus F a b := fun z ↦ h ▸ Set.mem_univ z
  choose U f hf hab using hz
  refine eq_of_forall_map_eq f ?_ hab
  exact Set.eq_univ_iff_forall.2 fun z ↦ Set.mem_iUnion.2 ⟨z, hf z⟩

lemma agreementLocus_self {T : Y.Etale} (a : F.obj.obj (op T)) :
    agreementLocus F a a = Set.univ :=
  Set.eq_univ_iff_forall.2 fun z ↦ ⟨T, 𝟙 T, ⟨z, rfl⟩, rfl⟩

/-- The agreement locus of the restrictions of two sections along a morphism `g : T' ⟶ T` of
étale `Y`-schemes is the preimage of the agreement locus. -/
lemma mem_agreementLocus_map_iff {T T' : Y.Etale} (g : T' ⟶ T) (a b : F.obj.obj (op T))
    (z : T'.left) :
    z ∈ agreementLocus F (F.obj.map g.op a) (F.obj.map g.op b) ↔
      g.left z ∈ agreementLocus F a b := by
  constructor
  · rintro ⟨U, f, ⟨u, rfl⟩, h⟩
    refine ⟨U, f ≫ g, ⟨u, rfl⟩, ?_⟩
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using h
  · rintro ⟨U, f, ⟨u, hu⟩, h⟩
    obtain ⟨Z, p₁, p₂, z', hp, hz₁, hz₂⟩ := exists_eq_of_apply_eq f g u z hu
    refine ⟨Z, p₂, ⟨z', hz₂⟩, ?_⟩
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ← hp]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, h]

/-- **Gluing along a jointly surjective family.** Sections over the members of a jointly
surjective family of étale morphisms which are compatible on all pairs of maps with a common
composite glue to a section. -/
lemma exists_eq_map_of_compatible {T : Y.Etale} {ι : Type*} {U : ι → Y.Etale}
    (f : ∀ i, U i ⟶ T) (hf : ⋃ i, Set.range (f i).left = Set.univ)
    (σ : ∀ i, F.obj.obj (op (U i)))
    (hσ : ∀ i j (Z : Y.Etale) (g₁ : Z ⟶ U i) (g₂ : Z ⟶ U j), g₁ ≫ f i = g₂ ≫ f j →
      F.obj.map g₁.op (σ i) = F.obj.map g₂.op (σ j)) :
    ∃ s : F.obj.obj (op T), ∀ i, F.obj.map (f i).op s = σ i := by
  have hmem := (ofArrows_mem_smallEtaleTopology_iff f).2 hf
  have hsh := isSheaf_forget (F := F) _ hmem
  rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hsh
  obtain ⟨s, hs, -⟩ := hsh σ fun i j Z g₁ g₂ h ↦ hσ i j Z g₁ g₂ h
  exact ⟨s, hs⟩

section Germs

/-- The forgetful functor of `ModuleCat.{u + 1} Λ` preserves filtered colimits of size `u`, the
size of the categories of pointed étale neighbourhoods of geometric points. -/
instance preservesFilteredColimitsOfSize_forget_moduleCat :
    PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ Y}

/-- A point of an étale `Y`-scheme lies in the agreement locus of two sections iff their germs
at a geometric point over it agree. -/
lemma mem_agreementLocus_iff_toPresheafFiber_eq {T : Y.Etale} (a b : F.obj.obj (op T))
    (z : Spec (.of Ω) ⟶ T.left) (hz : z ≫ T.hom = s) :
    z default ∈ agreementLocus F a b ↔
      (pointSmallEtale s).toPresheafFiber T (CategoryTheory.Over.homMk z hz) F.obj a =
        (pointSmallEtale s).toPresheafFiber T (CategoryTheory.Over.homMk z hz) F.obj b := by
  rw [GrothendieckTopology.Point.toPresheafFiber_eq_iff']
  constructor
  · rintro ⟨U, f, ⟨u, hu⟩, h⟩
    have := etale_left f
    obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed f.left z u hu
    refine ⟨U, f, CategoryTheory.Over.homMk l ?_, ?_, h⟩
    · change l ≫ U.hom = s
      rw [← MorphismProperty.Over.w f, ← Category.assoc, hl]
      exact hz
    · exact CategoryTheory.Over.OverMorphism.ext hl
  · rintro ⟨U, f, y, hy, h⟩
    obtain ⟨y', hy'⟩ : ∃ y' : Spec (.of Ω) ⟶ U.left, y' ≫ f.left = z :=
      ⟨y.left, congrArg CategoryTheory.CommaMorphism.left hy⟩
    refine ⟨U, f, ⟨y' default, ?_⟩, h⟩
    rw [← hy']
    rfl

end Germs

end AlgebraicGeometry.Etale
