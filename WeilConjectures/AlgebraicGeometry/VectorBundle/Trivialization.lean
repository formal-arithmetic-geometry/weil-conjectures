/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Zariski locally trivial vector bundles

A morphism `p : E ⟶ S` with a section `z : S ⟶ E` is a *vector bundle of rank `d`* if it is
Zariski locally on `S` isomorphic to the affine space `𝔸^d` with its zero section, by
trivialisations whose transition maps are linear. This is the form in which the vector bundle
`Spec_S (Sym 𝓔)` of a locally free module `𝓔` of rank `d` (blueprint
`def-asd-vector-bundle-zero-section`, `AlgebraicGeometry.Scheme.Modules.vectorBundle`) is used:
the notion is stable under base change, and the projection is smooth of relative dimension `d`.

## Main definitions

- `AlgebraicGeometry.VectorBundleTrivialization d p z`: a trivialisation of `(p, z)` over an open
  immersion `j : V ⟶ S`, i.e. a cartesian square `𝔸^d_V ⟶ E` over `V ⟶ S` carrying the zero
  section of `𝔸^d_V` to `z`.
- `AlgebraicGeometry.VectorBundleTrivialization.IsLinearlyCompatible`: two trivialisations differ
  locally on their overlap by an `AlgebraicGeometry.AffineSpace.linearMap`.
- `AlgebraicGeometry.VectorBundleAtlas d p z`: a family of pairwise linearly compatible
  trivialisations covering `S`.
- `AlgebraicGeometry.IsVectorBundleOfRank d p z`: `(p, z)` admits a vector bundle atlas.

## Main statements

- `AlgebraicGeometry.IsVectorBundleOfRank.baseChange`: vector bundles are stable under base change.
- `AlgebraicGeometry.IsVectorBundleOfRank.smoothOfRelativeDimension`: the projection of a vector
  bundle of rank `d` is smooth of relative dimension `d`.
- `AlgebraicGeometry.IsVectorBundleOfRank.isClosedImmersion`: the zero section is a closed
  immersion.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {E S : Scheme.{u}} (d : ℕ) (p : E ⟶ S) (z : S ⟶ E)

/-- A *trivialisation of rank `d`* of `p : E ⟶ S` with section `z` over an open immersion
`j : V ⟶ S`: a morphism `ι : 𝔸^d_V ⟶ E` exhibiting `𝔸^d_V` as the restriction of `E` to `V`
(the square formed with `p` and `j` is cartesian) and carrying the zero section of `𝔸^d_V` to
`z`. (blueprint: `def-asd-vector-bundle-zero-section`) -/
structure VectorBundleTrivialization where
  /-- The source of the open immersion. -/
  V : Scheme.{u}
  /-- The open immersion `V ⟶ S` over which the bundle is trivialised. -/
  j : V ⟶ S
  [isOpenImmersion : IsOpenImmersion j]
  /-- The identification `𝔸^d_V ≅ E|_V`, as a morphism to `E`. -/
  ι : 𝔸(ULift.{u} (Fin d); V) ⟶ E
  isPullback : IsPullback ι (𝔸(ULift.{u} (Fin d); V) ↘ V) p j
  zeroSection_ι : AffineSpace.zeroSection _ V ≫ ι = j ≫ z

attribute [instance] VectorBundleTrivialization.isOpenImmersion

namespace VectorBundleTrivialization

variable {d p z} (t : VectorBundleTrivialization d p z)

@[reassoc]
lemma ι_comp : t.ι ≫ p = 𝔸(ULift.{u} (Fin d); t.V) ↘ t.V ≫ t.j :=
  t.isPullback.w

instance : IsOpenImmersion t.ι :=
  MorphismProperty.of_isPullback t.isPullback.flip inferInstance

/-- Two trivialisations are *linearly compatible* if, locally on their overlap `W`, the
transition automorphism of `𝔸^d_W` is linear, i.e. given by a `d × d` matrix of functions. -/
def IsLinearlyCompatible (t t' : VectorBundleTrivialization d p z) : Prop :=
  ∀ w : ((pullback t.j t'.j : Scheme.{u}) : Type u), ∃ (W : Scheme.{u})
    (h : W ⟶ pullback t.j t'.j),
    IsOpenImmersion h ∧ w ∈ Set.range h ∧
    ∃ A : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) Γ(W, ⊤),
      AffineSpace.linearMap A ≫ AffineSpace.map _ (h ≫ pullback.snd t.j t'.j) ≫ t'.ι =
        AffineSpace.map _ (h ≫ pullback.fst t.j t'.j) ≫ t.ι

/-- Over the trivialising open `V`, the zero section `z` is the zero section of `𝔸^d_V`: the
square formed by the zero sections, `j` and `ι` is cartesian, provided `z` is a section of
`p`. -/
lemma isPullback_zeroSection (hz : z ≫ p = 𝟙 S) :
    IsPullback (AffineSpace.zeroSection _ t.V) t.j t.ι z := by
  refine IsPullback.of_right ?_ t.zeroSection_ι t.isPullback.flip
  rw [AffineSpace.zeroSection_over, hz]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The base change of a trivialisation along `g : S' ⟶ S`: a trivialisation of the pulled back
bundle over the pulled back open `V ×_S S'`. -/
@[simps V j]
noncomputable def baseChange (t : VectorBundleTrivialization d p z) {S' : Scheme.{u}}
    (g : S' ⟶ S) (hz : z ≫ p = 𝟙 S) :
    VectorBundleTrivialization d (pullback.snd p g)
      (pullback.lift (g ≫ z) (𝟙 S') (by simp [hz])) where
  V := Limits.pullback t.j g
  j := pullback.snd t.j g
  ι := pullback.lift (AffineSpace.map _ (pullback.fst t.j g) ≫ t.ι)
    (𝔸(ULift.{u} (Fin d); Limits.pullback t.j g) ↘ _ ≫ pullback.snd t.j g) (by
      rw [Category.assoc, t.ι_comp, AffineSpace.map_over_assoc, pullback.condition,
        Category.assoc])
  isPullback := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p g)
    rw [pullback.lift_fst, ← pullback.condition]
    exact (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) (pullback.fst t.j g)).paste_horiz
      t.isPullback
  zeroSection_ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst,
        ← Category.assoc, AffineSpace.zeroSection_comp_map, Category.assoc, t.zeroSection_ι,
        ← Category.assoc,
        pullback.condition, Category.assoc]
    · simp

@[reassoc (attr := simp)]
lemma baseChange_ι_fst {S' : Scheme.{u}} (g : S' ⟶ S) (hz : z ≫ p = 𝟙 S) :
    (t.baseChange g hz).ι ≫ Limits.pullback.fst p g =
      AffineSpace.map _ (Limits.pullback.fst t.j g) ≫ t.ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChange_ι_snd {S' : Scheme.{u}} (g : S' ⟶ S) (hz : z ≫ p = 𝟙 S) :
    (t.baseChange g hz).ι ≫ Limits.pullback.snd p g =
      𝔸(ULift.{u} (Fin d); (t.baseChange g hz).V) ↘ _ ≫ (t.baseChange g hz).j :=
  pullback.lift_snd _ _ _

lemma mem_range_baseChange_j {S' : Scheme.{u}} (g : S' ⟶ S) (hz : z ≫ p = 𝟙 S) (x : S')
    (hx : g x ∈ Set.range t.j) : x ∈ Set.range (t.baseChange g hz).j := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨q, -, hq⟩ := Scheme.Pullback.exists_preimage_pullback v x hv
  exact ⟨q, hq⟩

lemma IsLinearlyCompatible.baseChange {t t' : VectorBundleTrivialization d p z}
    (H : t.IsLinearlyCompatible t') {S' : Scheme.{u}} (g : S' ⟶ S) (hz : z ≫ p = 𝟙 S) :
    (t.baseChange g hz).IsLinearlyCompatible (t'.baseChange g hz) := by
  intro w'
  let φ : Limits.pullback (t.baseChange g hz).j (t'.baseChange g hz).j ⟶
      Limits.pullback t.j t'.j :=
    pullback.map _ _ _ _ (pullback.fst t.j g) (pullback.fst t'.j g) g
      pullback.condition.symm pullback.condition.symm
  obtain ⟨W, h, hh, ⟨w, hw⟩, A, hA⟩ := H (φ w')
  refine ⟨Limits.pullback h φ, pullback.snd h φ, inferInstance, ?_,
    A.map (pullback.fst h φ).appTop, ?_⟩
  · obtain ⟨q, -, hq⟩ := Scheme.Pullback.exists_preimage_pullback w w' hw
    exact ⟨q, hq⟩
  have hfst : pullback.snd h φ ≫ pullback.fst (t.baseChange g hz).j (t'.baseChange g hz).j ≫
      pullback.fst t.j g = pullback.fst h φ ≫ h ≫ pullback.fst t.j t'.j := by
    rw [pullback.condition_assoc]
    simp [φ]
  have hsnd : pullback.snd h φ ≫ pullback.snd (t.baseChange g hz).j (t'.baseChange g hz).j ≫
      pullback.fst t'.j g = pullback.fst h φ ≫ h ≫ pullback.snd t.j t'.j := by
    rw [pullback.condition_assoc]
    simp [φ]
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChange_ι_fst, ← AffineSpace.map_comp_assoc, hfst, hsnd]
    rw [AffineSpace.map_comp_assoc, ← AffineSpace.map_comp_linearMap_assoc,
      hA, ← AffineSpace.map_comp_assoc]
  · simp only [Category.assoc, baseChange_ι_snd, AffineSpace.map_over_assoc,
      AffineSpace.linearMap_over_assoc, pullback.condition]

end VectorBundleTrivialization

/-- A *vector bundle atlas of rank `d`* of `p : E ⟶ S` with section `z`: a family of pairwise
linearly compatible trivialisations whose opens cover `S`.
(blueprint: `def-asd-vector-bundle-zero-section`) -/
structure VectorBundleAtlas where
  /-- The index type of the atlas. -/
  I : Type u
  /-- The trivialisations of the atlas. -/
  trivialization : I → VectorBundleTrivialization d p z
  exists_mem_range (x : S) : ∃ i, x ∈ Set.range (trivialization i).j
  isLinearlyCompatible (i k : I) :
    (trivialization i).IsLinearlyCompatible (trivialization k)

namespace VectorBundleAtlas

variable {d p z}

/-- The open cover of the base by the trivialising opens of an atlas. -/
noncomputable def openCover (A : VectorBundleAtlas d p z) : S.OpenCover :=
  Scheme.Cover.mkOfCovers A.I (fun i ↦ (A.trivialization i).V) (fun i ↦ (A.trivialization i).j)
    A.exists_mem_range

/-- The zero section of a vector bundle is a section of its projection. -/
lemma comp_eq_id (A : VectorBundleAtlas d p z) : z ≫ p = 𝟙 S := by
  refine A.openCover.hom_ext _ _ fun i ↦ ?_
  change (A.trivialization i).j ≫ z ≫ p = (A.trivialization i).j ≫ 𝟙 S
  rw [← Category.assoc, ← (A.trivialization i).zeroSection_ι, Category.assoc,
    (A.trivialization i).ι_comp, AffineSpace.zeroSection_over_assoc, Category.comp_id]

/-- The base change of a vector bundle atlas along `g : S' ⟶ S`. -/
@[simps I]
noncomputable def baseChange (A : VectorBundleAtlas d p z) {S' : Scheme.{u}} (g : S' ⟶ S) :
    VectorBundleAtlas d (pullback.snd p g)
      (pullback.lift (g ≫ z) (𝟙 S') (by simp [A.comp_eq_id])) where
  I := A.I
  trivialization i := (A.trivialization i).baseChange g A.comp_eq_id
  exists_mem_range x := by
    obtain ⟨i, hi⟩ := A.exists_mem_range (g x)
    exact ⟨i, (A.trivialization i).mem_range_baseChange_j g A.comp_eq_id x hi⟩
  isLinearlyCompatible i k := (A.isLinearlyCompatible i k).baseChange g A.comp_eq_id

end VectorBundleAtlas

/-- `p : E ⟶ S` with section `z : S ⟶ E` is a *vector bundle of rank `d`*: Zariski locally on
`S` it is isomorphic to `𝔸^d` with its zero section, by trivialisations whose transition maps
are linear (`AlgebraicGeometry.VectorBundleAtlas`).
(blueprint: `def-asd-vector-bundle-zero-section`) -/
class IsVectorBundleOfRank : Prop where
  nonempty_atlas : Nonempty (VectorBundleAtlas d p z)

namespace IsVectorBundleOfRank

variable {d p z} [h : IsVectorBundleOfRank d p z]
include h

/-- A chosen vector bundle atlas. -/
noncomputable def atlas : VectorBundleAtlas d p z :=
  h.nonempty_atlas.some

/-- The zero section of a vector bundle is a section of the projection. -/
lemma comp_eq_id : z ≫ p = 𝟙 S :=
  (atlas (d := d)).comp_eq_id

lemma exists_trivialization (x : S) :
    ∃ t : VectorBundleTrivialization d p z, x ∈ Set.range t.j := by
  obtain ⟨i, hi⟩ := (atlas (d := d) (p := p) (z := z)).exists_mem_range x
  exact ⟨_, hi⟩

/-- Vector bundles are stable under base change. -/
instance baseChange {S' : Scheme.{u}} (g : S' ⟶ S) :
    IsVectorBundleOfRank d (Limits.pullback.snd p g)
      (Limits.pullback.lift (g ≫ z) (𝟙 S') (by simp [comp_eq_id (d := d)])) :=
  ⟨⟨(atlas (d := d) (p := p) (z := z)).baseChange g⟩⟩

/-- A property of morphisms local at the target and satisfied by the projection of `𝔸^d` holds
for the projection of a vector bundle of rank `d`. -/
lemma of_isZariskiLocalAtTarget (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V : Scheme.{u}, P (𝔸(ULift.{u} (Fin d); V) ↘ V)) : P p := by
  refine IsZariskiLocalAtTarget.of_forall_exists_isPullback p fun x ↦ ?_
  obtain ⟨t, ht⟩ := exists_trivialization (d := d) (p := p) (z := z) x
  exact ⟨_, _, t.ι, _, t.j, inferInstance, ht, t.isPullback, hP _⟩

/-- The projection of a vector bundle of rank `d` is smooth of relative dimension `d`. -/
lemma smoothOfRelativeDimension : SmoothOfRelativeDimension d p :=
  of_isZariskiLocalAtTarget (z := z) (@SmoothOfRelativeDimension d) fun V ↦ by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) V

/-- The projection of a vector bundle is affine. -/
lemma isAffineHom : IsAffineHom p :=
  of_isZariskiLocalAtTarget (d := d) (z := z) @IsAffineHom fun _ ↦ inferInstance

/-- The zero section of a vector bundle is a closed immersion. -/
lemma isClosedImmersion : IsClosedImmersion z := by
  refine IsZariskiLocalAtTarget.of_forall_exists_isPullback z fun e ↦ ?_
  obtain ⟨t, v, hv⟩ := exists_trivialization (d := d) (p := p) (z := z) (p e)
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback e v hv.symm
  refine ⟨_, _, t.j, AffineSpace.zeroSection _ t.V, t.ι, inferInstance,
    ⟨t.isPullback.isoPullback.inv q, ?_⟩, (t.isPullback_zeroSection (comp_eq_id (d := d))).flip,
    inferInstance⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hq]

end IsVectorBundleOfRank

/-- The trivial vector bundle atlas of `𝔸^d_S`, with the single trivialisation `𝟙`. -/
noncomputable def VectorBundleAtlas.affineSpace (S : Scheme.{u}) :
    VectorBundleAtlas d (𝔸(ULift.{u} (Fin d); S) ↘ S) (AffineSpace.zeroSection _ S) where
  I := PUnit
  trivialization _ :=
    { V := S
      j := 𝟙 S
      ι := 𝟙 _
      isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩
      zeroSection_ι := by simp }
  exists_mem_range x := ⟨⟨⟩, x, rfl⟩
  isLinearlyCompatible _ _ w := by
    refine ⟨_, 𝟙 _, inferInstance, ⟨w, rfl⟩, 1, ?_⟩
    simp only [AffineSpace.linearMap_one, Category.id_comp, Category.comp_id]
    congr 1
    simpa using (pullback.condition (f := 𝟙 S) (g := 𝟙 S)).symm

/-- The trivial vector bundle `𝔸^d_S` with its zero section. -/
instance isVectorBundleOfRank_affineSpace (S : Scheme.{u}) :
    IsVectorBundleOfRank d (𝔸(ULift.{u} (Fin d); S) ↘ S) (AffineSpace.zeroSection _ S) :=
  ⟨⟨VectorBundleAtlas.affineSpace d S⟩⟩

end AlgebraicGeometry
