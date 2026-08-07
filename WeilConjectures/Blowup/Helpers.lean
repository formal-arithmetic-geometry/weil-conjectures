/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib

/-!

# Helper lemmas for the blow-up construction

General purpose lemmas missing from Mathlib that the blow-up construction relies on:

- `AlgebraicGeometry.GradedRingHom.gradeZeroRingHom` — the degree-zero component of a graded
  ring homomorphism as a ring homomorphism between the degree-zero subrings.
- `AlgebraicGeometry.Proj.map_toSpecZero` — naturality of `Proj.toSpecZero` with respect to
  `Proj.map`.
- `AlgebraicGeometry.IsPullback.isOpenImmersion_fst` /
  `AlgebraicGeometry.IsPullback.opensRange_fst` — in a pullback square of schemes whose
  bottom is an open immersion, the top is an open immersion with range the preimage of the
  range of the bottom.
- `AlgebraicGeometry.morphismRestrictArrowIso` — transport of a morphism restriction along
  compatible open immersions.

-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry

section GradeZero

variable {ι A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [DecidableEq ι] [AddCommMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The degree-zero component of a graded ring homomorphism, as a ring homomorphism
between the degree-zero subrings. -/
def _root_.GradedRingHom.gradeZeroRingHom (f : 𝒜 →+*ᵍ ℬ) : 𝒜 0 →+* ℬ 0 where
  toFun a := ⟨f a, f.map_mem a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
lemma _root_.GradedRingHom.coe_gradeZeroRingHom_apply (f : 𝒜 →+*ᵍ ℬ) (a : 𝒜 0) :
    (f.gradeZeroRingHom a : B) = f a :=
  rfl

/-- `HomogeneousLocalization.Away.map` is compatible with the canonical ring homomorphisms
from the degree-zero subrings. -/
lemma _root_.HomogeneousLocalization.Away.map_comp_fromZeroRingHom (g : 𝒜 →+*ᵍ ℬ) (s : A) :
    (HomogeneousLocalization.Away.map g s).comp
        (fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (fromZeroRingHom ℬ (Submonoid.powers (g s))).comp g.gradeZeroRingHom := by
  ext a
  simp [fromZeroRingHom, HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]

end GradeZero

section ProjMap

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- `Proj.map` only depends on the underlying graded ring homomorphism. -/
lemma Proj.map_congr {f g : 𝒜 →+*ᵍ ℬ} (e : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst e; rfl

/-- Naturality of `Proj.toSpecZero` with respect to `Proj.map`: the square

```
Proj ℬ  ⟶  Proj 𝒜
  |            |
  v            v
Spec (ℬ 0) ⟶ Spec (𝒜 0)
```

commutes. -/
lemma Proj.map_toSpecZero (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradeZeroRingHom) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [Proj.awayι_comp_map_assoc f hf s.1.2 _ s.2.2, Proj.awayι_toSpecZero,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    HomogeneousLocalization.Away.map_comp_fromZeroRingHom]

end ProjMap

section Pullback

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- In a pullback square of schemes whose bottom is an open immersion, the top is an open
immersion. -/
lemma _root_.CategoryTheory.IsPullback.isOpenImmersion_fst [IsOpenImmersion g]
    (h : IsPullback fst snd f g) : IsOpenImmersion fst :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance

/-- In a pullback square of schemes whose bottom `g` is an open immersion, the range of the
top is the preimage under `f` of the range of `g`. -/
lemma _root_.CategoryTheory.IsPullback.opensRange_fst [IsOpenImmersion g]
    (h : IsPullback fst snd f g) :
    haveI : IsOpenImmersion fst := h.isOpenImmersion_fst
    fst.opensRange = f ⁻¹ᵁ g.opensRange := by
  haveI : IsOpenImmersion fst := h.isOpenImmersion_fst
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨snd p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    have e : h.isoPullback.inv ≫ fst = Limits.pullback.fst f g := by
      rw [Iso.inv_comp_eq, h.isoPullback_hom_fst]
    exact ⟨h.isoPullback.inv p, by rw [← Scheme.Hom.comp_apply, e]; exact hp⟩

end Pullback

section RestrictArrow

variable {X Y Z Z' : Scheme.{u}}

/-- If `e ≫ f = q ≫ j` with `e`, `j` open immersions and `f ⁻¹ᵁ (range j) = range e`, then
the restriction `f ∣_ j.opensRange` is isomorphic to `q` in the arrow category. -/
noncomputable def morphismRestrictArrowIso (f : X ⟶ Y) {e : Z ⟶ X} {j : Z' ⟶ Y}
    (q : Z ⟶ Z') [IsOpenImmersion e] [IsOpenImmersion j]
    (w : e ≫ f = q ≫ j) (h : f ⁻¹ᵁ j.opensRange = e.opensRange) :
    Arrow.mk (f ∣_ j.opensRange) ≅ Arrow.mk q := by
  have hα : Set.range ⇑(f ⁻¹ᵁ j.opensRange).ι = Set.range ⇑e := by
    rw [Scheme.Opens.range_ι, h]; rfl
  have hβ : Set.range ⇑j.opensRange.ι = Set.range ⇑j := by
    rw [Scheme.Opens.range_ι]; rfl
  refine Arrow.isoMk' (f ∣_ j.opensRange) q
    (IsOpenImmersion.isoOfRangeEq (f ⁻¹ᵁ j.opensRange).ι e hα)
    (IsOpenImmersion.isoOfRangeEq j.opensRange.ι j hβ) ?_
  rw [← cancel_mono j, Category.assoc, Category.assoc, ← w,
    IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι]

end RestrictArrow

section OpensExt

/-- Two open subsets of a scheme agree if their preimages under every chart of an open
cover agree. -/
lemma Scheme.Opens.ext_of_openCover {Y : Scheme.{u}} (𝒰 : Y.OpenCover) {U V : Y.Opens}
    (h : ∀ i, 𝒰.f i ⁻¹ᵁ U = 𝒰.f i ⁻¹ᵁ V) : U = V := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_)
  obtain ⟨y, hy⟩ := 𝒰.covers x
  rw [← hy]
  constructor
  · intro hx
    have hyU : y ∈ 𝒰.f (𝒰.idx x) ⁻¹ᵁ U := hx
    rw [h] at hyU
    exact hyU
  · intro hx
    have hyV : y ∈ 𝒰.f (𝒰.idx x) ⁻¹ᵁ V := hx
    rw [← h] at hyV
    exact hyV

end OpensExt

instance : MorphismProperty.RespectsRight @IsOpenImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf ↦ by
    haveI : IsOpenImmersion i := hi
    haveI : IsOpenImmersion f := hf
    infer_instance⟩

end AlgebraicGeometry
