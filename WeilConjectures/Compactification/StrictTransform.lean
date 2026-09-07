/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Blowup.Complement
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!

# Strict transforms

This file defines the strict transform of a morphism `f : Y ⟶ X` along a morphism
`π : X' ⟶ X` (in practice a blow-up) preserving an open `U ⊆ X`.

Given `f : Y ⟶ X`, `π : X' ⟶ X` and an open `U ⊆ X`, the fibre product `Y ×_X X'`
contains the open locus lying over `U`. The strict transform of `Y` is the
scheme-theoretic image of this open locus inside `Y ×_X X'`
(blueprint: `def:nagata-strict-transform`). For a blow-up `π = Bl_I(X) ⟶ X` and `U` the
complement of the support of `I`, this recovers the classical strict transform; the
specialization is `AlgebraicGeometry.Scheme.IdealSheafData.strictTransform`.

## Main definitions

- `AlgebraicGeometry.strictTransformOpen f π U`: the open locus of `Y ×_X X'` over `U`;
- `AlgebraicGeometry.strictTransform f π U`: the strict transform, i.e. the
  scheme-theoretic image of the open locus in `Y ×_X X'`
  (blueprint: `def:nagata-strict-transform`);
- `AlgebraicGeometry.strictTransformι`: the closed immersion into `Y ×_X X'`;
- `AlgebraicGeometry.Scheme.IdealSheafData.strictTransform I f`: the strict transform
  of `f` along the blow-up of the ideal sheaf `I`, preserving the complement of the
  support of `I`.

## Main results

- separatedness, quasi-compactness, local finite type and being a closed immersion of
  `AlgebraicGeometry.strictTransformMap`, inherited from the transformed morphism;
- `AlgebraicGeometry.isIso_pullback_fst_strictTransformι`: the strict transform
  contains the whole open locus over `U`;
- the underlying set of the strict transform is squeezed between the inverse image of
  the `U`-part of the image (`mem_range_strictTransformMap_of_mem_of_mem_range`) and
  the full inverse image of the image
  (`range_strictTransformMap_subset_preimage_range`); consequently
  disjointness of closed subschemes persists along strict transforms
  (`disjoint_range_strictTransformMap_of_disjoint`; blueprint:
  `lemma:nagata-boundary-disjoint-persists`; proof order item 37);
- `AlgebraicGeometry.isPullback_strictTransformOpen`: if `π` is an isomorphism over
  `U`, the open locus is canonically `Y ×_X U`;
- `AlgebraicGeometry.isPullback_strictTransform_over`: the combination of the previous
  two, identifying the part of the strict transform lying over `U` with the ordinary base
  change `Y ×_X U` (blueprint: `lemma:nagata-strict-transform-over-complement`);
- `AlgebraicGeometry.quasiCompact_strictTransformOpen_ι`: if `f` and `π` are
  quasi-compact, `Y ×_X X'` is quasi-separated and `U` is a quasi-compact open, then
  `(strictTransformOpen f π U).ι` is quasi-compact;
- `AlgebraicGeometry.ker_strictTransformMap`: when the inclusion of the open locus is
  quasi-compact, the strict transform and its open locus have the same scheme-theoretic
  image in `X'`;
- `AlgebraicGeometry.ker_eq_ker_strictTransformMap`: if `π` is an isomorphism over `U`
  and `h : V ⟶ X` is quasi-compact with range in `U`, then the scheme-theoretic image of
  a lift `h' : V ⟶ X'` of `h` is the strict transform of the scheme-theoretic image of
  `h` (blueprint: `lemma:nagata-scheme-image-transport-strict-transform`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y X' : Scheme.{u}} (f : Y ⟶ X) (π : X' ⟶ X) (U : X.Opens)

/-- The open locus of the fibre product `Y ×_X X'` lying over the open `U ⊆ X`. -/
def strictTransformOpen : (pullback f π).Opens :=
  pullback.snd f π ⁻¹ᵁ (π ⁻¹ᵁ U)

/-- The open locus over `U` is the preimage of `U` under the structure morphism of the
fibre product to the base. -/
lemma strictTransformOpen_eq_preimage :
    strictTransformOpen f π U = (pullback.fst f π ≫ f) ⁻¹ᵁ U := by
  rw [strictTransformOpen, ← Scheme.Hom.comp_preimage, pullback.condition]

/-- If the fibre product `Y ×_X X'` is quasi-separated, `f` and `π` are quasi-compact and
`U` is a quasi-compact open of `X`, then the inclusion of the open locus over `U` is a
quasi-compact morphism. -/
theorem quasiCompact_strictTransformOpen_ι [QuasiSeparatedSpace ↥(pullback f π)]
    [QuasiCompact f] [QuasiCompact π] (hU : IsCompact (U : Set X)) :
    QuasiCompact (strictTransformOpen f π U).ι := by
  have : QuasiCompact (pullback.fst f π) := MorphismProperty.pullback_fst _ _ ‹_›
  refine Scheme.Opens.quasiCompact_ι _ ?_
  rw [strictTransformOpen_eq_preimage]
  exact (pullback.fst f π ≫ f).isCompact_preimage hU

/-- The strict transform of `f : Y ⟶ X` along `π : X' ⟶ X` relative to the open
`U ⊆ X`: the scheme-theoretic image of the open locus of `Y ×_X X'` lying over `U`.
For `π` the blow-up of an ideal with support complement `U` this is the classical
strict transform. (Blueprint: `def:nagata-strict-transform`.) -/
def strictTransform : Scheme.{u} :=
  ((strictTransformOpen f π U).ι).image

/-- The closed immersion of the strict transform into the fibre product `Y ×_X X'`. -/
def strictTransformι : strictTransform f π U ⟶ pullback f π :=
  ((strictTransformOpen f π U).ι).imageι

instance : IsClosedImmersion (strictTransformι f π U) :=
  inferInstanceAs (IsClosedImmersion ((strictTransformOpen f π U).ι).imageι)

/-- The factorization of the open locus over `U` through the strict transform. -/
def strictTransformFactor : (strictTransformOpen f π U).toScheme ⟶ strictTransform f π U :=
  ((strictTransformOpen f π U).ι).toImage

@[reassoc (attr := simp)]
lemma strictTransformFactor_ι :
    strictTransformFactor f π U ≫ strictTransformι f π U = (strictTransformOpen f π U).ι :=
  ((strictTransformOpen f π U).ι).toImage_imageι

/-- The structure morphism of the strict transform to the modified scheme `X'`. -/
def strictTransformMap : strictTransform f π U ⟶ X' :=
  strictTransformι f π U ≫ pullback.snd f π

/-- The projection of the strict transform to the original source `Y`. -/
def strictTransformToSource : strictTransform f π U ⟶ Y :=
  strictTransformι f π U ≫ pullback.fst f π

/-- The factorization of the open locus through the strict transform covers the
projection of the fibre product to the modified scheme. -/
@[reassoc (attr := simp)]
lemma strictTransformFactor_strictTransformMap :
    strictTransformFactor f π U ≫ strictTransformMap f π U =
      (strictTransformOpen f π U).ι ≫ pullback.snd f π := by
  simp only [strictTransformMap, strictTransformFactor_ι_assoc]

/-- The strict-transform projection and the projection to the source cover the same
morphism to the base: the square

```
strictTransform f π U --strictTransformMap--> X'
        |                                     |
strictTransformToSource                       π
        ↓                                     ↓
        Y ----------------- f --------------> X
```

commutes. -/
@[reassoc]
lemma strictTransform_condition :
    strictTransformToSource f π U ≫ f = strictTransformMap f π U ≫ π := by
  simp only [strictTransformToSource, strictTransformMap, Category.assoc, pullback.condition]

/-! The strict transform of a morphism is a closed subscheme of the base change, so
separatedness, quasi-compactness, local finite type and being a closed immersion are
inherited from `f`. -/

instance [IsSeparated f] : IsSeparated (strictTransformMap f π U) :=
  have : IsSeparated (pullback.snd f π) := MorphismProperty.pullback_snd _ _ ‹_›
  inferInstanceAs (IsSeparated (strictTransformι f π U ≫ pullback.snd f π))

instance [QuasiCompact f] : QuasiCompact (strictTransformMap f π U) :=
  inferInstanceAs (QuasiCompact (strictTransformι f π U ≫ pullback.snd f π))

instance [LocallyOfFiniteType f] : LocallyOfFiniteType (strictTransformMap f π U) :=
  have : LocallyOfFiniteType (pullback.snd f π) := MorphismProperty.pullback_snd _ _ ‹_›
  inferInstanceAs (LocallyOfFiniteType (strictTransformι f π U ≫ pullback.snd f π))

instance [IsClosedImmersion f] : IsClosedImmersion (strictTransformMap f π U) :=
  have : IsClosedImmersion (pullback.snd f π) := MorphismProperty.pullback_snd _ _ ‹_›
  inferInstanceAs (IsClosedImmersion (strictTransformι f π U ≫ pullback.snd f π))

/-- The ideal sheaf cutting out the strict transform is the kernel of the open locus. -/
lemma ker_strictTransformι :
    (strictTransformι f π U).ker = ((strictTransformOpen f π U).ι).ker :=
  Scheme.IdealSheafData.ker_subschemeι _

section SchemeTheoreticImage

variable [QuasiCompact (strictTransformOpen f π U).ι]

/-- The factorization of the open locus through the strict transform is
scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_strictTransformFactor :
    IsSchemeTheoreticallyDominant (strictTransformFactor f π U) :=
  inferInstanceAs (IsSchemeTheoreticallyDominant ((strictTransformOpen f π U).ι).toImage)

/-- **The strict transform and its open locus have the same scheme-theoretic image in
`X'`**: in the commutative diagram

```
strictTransformOpen f π U --ι--> Y ×_X X' --snd--> X'
           \                                      ↗
  strictTransformFactor            strictTransformMap
             ↘                          /
              strictTransform f π U
```

the two composites `strictTransformOpen f π U ⟶ X'` agree, and the left-hand
factorization is scheme-theoretically dominant. -/
theorem ker_strictTransformMap :
    (strictTransformMap f π U).ker =
      ((strictTransformOpen f π U).ι ≫ pullback.snd f π).ker := by
  rw [← strictTransformFactor_ι, Category.assoc, strictTransformMap]
  exact (Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant _ _).symm

end SchemeTheoreticImage

section Range

/-! ### The underlying set of the strict transform

The strict transform of `f` is squeezed between the inverse image of the `U`-part of
the image of `f` and the full inverse image of the image of `f`; consequently
disjointness of images persists along strict transforms. -/

/-- The strict transform of `f` lies inside the full inverse image of the image of
`f`: the range of the strict-transform projection is contained in `π ⁻¹ (range f)`. -/
theorem range_strictTransformMap_subset_preimage_range :
    Set.range (strictTransformMap f π U) ⊆ π ⁻¹' Set.range f := by
  rintro _ ⟨t, rfl⟩
  refine ⟨strictTransformToSource f π U t, ?_⟩
  calc f (strictTransformToSource f π U t)
      = (strictTransformToSource f π U ≫ f) t := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (strictTransformMap f π U ≫ π) t := by rw [strictTransform_condition]
    _ = π (strictTransformMap f π U t) := Scheme.Hom.comp_apply _ _ _

/-- The strict transform of `f` contains the whole locus over the preserved open: a
point of `X'` lying over `U` and over the image of `f` is in the range of the
strict-transform projection. -/
theorem mem_range_strictTransformMap_of_mem_of_mem_range {x' : X'} (hU : π x' ∈ U)
    (hf : π x' ∈ Set.range f) :
    x' ∈ Set.range (strictTransformMap f π U) := by
  obtain ⟨y, hy⟩ := hf
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback y x' hy
  have hwU : w ∈ strictTransformOpen f π U := by
    change π (pullback.snd f π w) ∈ U
    rw [hw2]
    exact hU
  obtain ⟨w₀, rfl⟩ : w ∈ Set.range (strictTransformOpen f π U).ι := by
    rwa [Scheme.Opens.range_ι]
  refine ⟨strictTransformFactor f π U w₀, ?_⟩
  calc strictTransformMap f π U (strictTransformFactor f π U w₀)
      = (strictTransformFactor f π U ≫ strictTransformMap f π U) w₀ :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = ((strictTransformOpen f π U).ι ≫ pullback.snd f π) w₀ := by
        rw [strictTransformFactor_strictTransformMap]
    _ = pullback.snd f π ((strictTransformOpen f π U).ι w₀) := Scheme.Hom.comp_apply _ _ _
    _ = x' := hw2

/-- **Disjointness of boundary closures persists along strict transforms**
(blueprint: `lemma:nagata-boundary-disjoint-persists`; proof order item 37): if two
closed subschemes have disjoint images, their strict transforms along an arbitrary
morphism `π : X' ⟶ X` remain disjoint, because each strict transform is contained
in the full inverse image of the corresponding closed subscheme. -/
theorem disjoint_range_strictTransformMap_of_disjoint {Y₁ Y₂ : Scheme.{u}}
    (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) (hdisj : Disjoint (Set.range f₁) (Set.range f₂)) :
    Disjoint (Set.range (strictTransformMap f₁ π U))
      (Set.range (strictTransformMap f₂ π U)) :=
  (hdisj.preimage π).mono
    (range_strictTransformMap_subset_preimage_range f₁ π U)
    (range_strictTransformMap_subset_preimage_range f₂ π U)

end Range

section OverComplement

/-- Over the preserved open locus, the ideal sheaf cutting out the strict transform
vanishes: nothing is lost over `U`.
(Blueprint: `lemma:nagata-strict-transform-over-complement`.) -/
theorem strictTransform_ker_comap_openι :
    ((strictTransformOpen f π U).ι).ker.comap (strictTransformOpen f π U).ι = ⊥ :=
  Scheme.Hom.comap_ker_self _

/-- The strict transform contains the whole open locus over `U`: the base change of the
closed immersion `strictTransform f π U ⟶ Y ×_X X'` to the open locus over `U` is an
isomorphism. (Blueprint: `lemma:nagata-strict-transform-over-complement`.) -/
instance isIso_pullback_fst_strictTransformι :
    IsIso (pullback.fst (strictTransformOpen f π U).ι (strictTransformι f π U)) := by
  have h1 : (pullback.fst (strictTransformOpen f π U).ι (strictTransformι f π U)).ker = ⊥ := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ker_strictTransformι,
      strictTransform_ker_comap_openι]
  exact IsClosedImmersion.isIso_of_ker_eq _ (𝟙 _) _ (Category.comp_id _) (by simp [h1])

end OverComplement

section PullbackComparison

variable [IsIso (π ∣_ U)]

/-- If `π : X' ⟶ X` restricts to an isomorphism over `U` — for instance if `π` is the
blow-up of an ideal whose support is disjoint from `U` — then the open locus of
`Y ×_X X'` over `U` is canonically the ordinary pullback `Y ×_X U`, compatibly with the
projection to `Y`.
(Blueprint: `lemma:nagata-strict-transform-over-complement`.) -/
theorem isPullback_strictTransformOpen :
    IsPullback ((strictTransformOpen f π U).ι ≫ pullback.fst f π)
      ((pullback.snd f π ∣_ (π ⁻¹ᵁ U)) ≫ (π ∣_ U)) f U.ι := by
  have C1 : IsPullback (strictTransformOpen f π U).ι (pullback.snd f π ∣_ (π ⁻¹ᵁ U))
      (pullback.snd f π) (π ⁻¹ᵁ U).ι :=
    (isPullback_morphismRestrict (pullback.snd f π) (π ⁻¹ᵁ U)).flip
  have M := C1.paste_horiz (IsPullback.of_hasPullback f π)
  refine M.of_iso (Iso.refl _) (Iso.refl _) (asIso (π ∣_ U)) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp [morphismRestrict_ι]

/-- The strict transform over the preserved open: combining
`AlgebraicGeometry.isIso_pullback_fst_strictTransformι` with
`AlgebraicGeometry.isPullback_strictTransformOpen`, the part of the strict transform lying
over `U` is the ordinary base change `Y ×_X U`.
(Blueprint: `lemma:nagata-strict-transform-over-complement`.) -/
theorem isPullback_strictTransform_over :
    IsPullback
      (pullback.fst (strictTransformOpen f π U).ι (strictTransformι f π U) ≫
        (strictTransformOpen f π U).ι ≫ pullback.fst f π)
      (pullback.fst (strictTransformOpen f π U).ι (strictTransformι f π U) ≫
        (pullback.snd f π ∣_ (π ⁻¹ᵁ U)) ≫ (π ∣_ U))
      f U.ι := by
  refine (isPullback_strictTransformOpen f π U).of_iso
    (asIso (pullback.fst (strictTransformOpen f π U).ι (strictTransformι f π U))).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp

/-- **Transport of a scheme-theoretic image through a morphism that is an isomorphism
over `U`** (blueprint: `lemma:nagata-scheme-image-transport-strict-transform`): if
`h : V ⟶ X` is quasi-compact with range inside `U`, and `h' : V ⟶ X'` is a lift of `h`
along `π`, then the scheme-theoretic image of `h'` is the strict transform of the
scheme-theoretic image of `h`. Both images are recorded by their kernel ideal sheaves.

```
              V
         h'  ↙ ↘  h
           ↙     ↘
         X' --π--> X
```

The lift exists and is unique (`AlgebraicGeometry.Scheme.Hom.liftOfIsIsoRestrict` and
`AlgebraicGeometry.Scheme.Hom.hom_ext_of_isIso_restrict`), but it is taken as data here
because in the applications it is produced by a different construction.

The right-hand side is a strict transform, so the theorem carries the standing
quasi-compactness assumption of this section: the inclusion of the open locus over `U`
must be a quasi-compact morphism. It is not implied by the remaining hypotheses, and is
discharged from finiteness data by
`AlgebraicGeometry.quasiCompact_strictTransformOpen_ι`. -/
theorem ker_eq_ker_strictTransformMap {V : Scheme.{u}} (h : V ⟶ X) [QuasiCompact h]
    (hrange : Set.range h ⊆ (U : Set X)) (h' : V ⟶ X') (hlift : h' ≫ π = h)
    [QuasiCompact (strictTransformOpen h.imageι π U).ι] :
    h'.ker = (strictTransformMap h.imageι π U).ker := by
  set L := strictTransformOpen h.imageι π U
  -- The open locus is the restriction of `SIm(h)` over `U`.
  have hPB := isPullback_strictTransformOpen h.imageι π U
  -- The lift of `h` to `SIm(h) ×_X X'`.
  have hcond : h.toImage ≫ h.imageι = h' ≫ π := by rw [Scheme.Hom.toImage_imageι, hlift]
  set k := pullback.lift h.toImage h' hcond
  have hkfst : k ≫ pullback.fst h.imageι π = h.toImage := pullback.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd h.imageι π = h' := pullback.lift_snd _ _ _
  -- It lands in the open locus, because `h'` lands over `U`, hence in `π ⁻¹ᵁ U`.
  have hkrange : Set.range (k ≫ pullback.snd h.imageι π) ⊆ ((π ⁻¹ᵁ U : X'.Opens) : Set X') := by
    rw [hksnd, ← Scheme.Opens.range_ι]
    exact range_subset_range_preimage_ι π U h' (by rwa [hlift])
  set m := (pullback.snd h.imageι π).liftPreimage (π ⁻¹ᵁ U) k hkrange
  have hmfac : m ≫ L.ι = k := (pullback.snd h.imageι π).liftPreimage_ι (π ⁻¹ᵁ U) k hkrange
  -- The projection of the open locus to `SIm(h)` is a base change of the open immersion
  -- `U ⟶ X`, so `V` sits inside the open locus as a flat base change of `V ⟶ SIm(h)`,
  -- and scheme-theoretic dominance descends.
  have hopen : IsOpenImmersion (L.ι ≫ pullback.fst h.imageι π) :=
    IsOpenImmersion.of_isPullback hPB.flip inferInstance
  have hsq : IsPullback (𝟙 V) m h.toImage (L.ι ≫ pullback.fst h.imageι π) :=
    IsPullback.of_horiz_isIso_mono
      ⟨by rw [Category.id_comp, ← Category.assoc, hmfac, hkfst]⟩
  have hdom : IsSchemeTheoreticallyDominant m := .of_isPullback hsq
  calc h'.ker
      = (m ≫ L.ι ≫ pullback.snd h.imageι π).ker := by rw [← Category.assoc, hmfac, hksnd]
    _ = (L.ι ≫ pullback.snd h.imageι π).ker :=
        Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant _ _
    _ = _ := (ker_strictTransformMap h.imageι π U).symm

end PullbackComparison

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)

/-- The strict transform of `f : Y ⟶ X` along the blow-up of the ideal sheaf `I`,
preserving the complement of the support of `I`.
(Blueprint: `def:nagata-strict-transform`.) -/
def strictTransform : Scheme.{u} :=
  AlgebraicGeometry.strictTransform f I.blowupMap I.support.compl

/-- The closed immersion of the strict transform along a blow-up into `Y ×_X Bl_I X`. -/
def strictTransformι : I.strictTransform f ⟶ pullback f I.blowupMap :=
  AlgebraicGeometry.strictTransformι f I.blowupMap I.support.compl

instance : IsClosedImmersion (I.strictTransformι f) :=
  inferInstanceAs (IsClosedImmersion (AlgebraicGeometry.strictTransformι _ _ _))

/-- Away from the centre, the open locus of `Y ×_X Bl_I X` over the complement of the
support of `I` is canonically the ordinary pullback, compatibly with the projection
to `Y`. This combines the blow-up complement theorem
(`thm:nagata-global-blowup-complement`) with the strict transform comparison.
(Blueprint: `lemma:nagata-strict-transform-over-complement`.) -/
theorem isPullback_strictTransformOpen_blowupMap :
    IsPullback
      ((strictTransformOpen f I.blowupMap I.support.compl).ι ≫ pullback.fst f I.blowupMap)
      ((pullback.snd f I.blowupMap ∣_ (I.blowupMap ⁻¹ᵁ I.support.compl)) ≫
        (I.blowupMap ∣_ I.support.compl))
      f (Scheme.Opens.ι I.support.compl) :=
  have := I.isIso_blowupMap_restrict_support_compl
  AlgebraicGeometry.isPullback_strictTransformOpen f I.blowupMap I.support.compl

/-- The strict transform along a blow-up agrees with the ordinary base change over the
complement of the centre.
(Blueprint: `lemma:nagata-strict-transform-over-complement`.) -/
theorem isPullback_strictTransform_over_blowupMap :
    IsPullback
      (pullback.fst (strictTransformOpen f I.blowupMap I.support.compl).ι
          (AlgebraicGeometry.strictTransformι f I.blowupMap I.support.compl) ≫
        (strictTransformOpen f I.blowupMap I.support.compl).ι ≫ pullback.fst f I.blowupMap)
      (pullback.fst (strictTransformOpen f I.blowupMap I.support.compl).ι
          (AlgebraicGeometry.strictTransformι f I.blowupMap I.support.compl) ≫
        (pullback.snd f I.blowupMap ∣_ (I.blowupMap ⁻¹ᵁ I.support.compl)) ≫
        (I.blowupMap ∣_ I.support.compl))
      f (Scheme.Opens.ι I.support.compl) :=
  have := I.isIso_blowupMap_restrict_support_compl
  AlgebraicGeometry.isPullback_strictTransform_over f I.blowupMap I.support.compl

end AlgebraicGeometry.Scheme.IdealSheafData
