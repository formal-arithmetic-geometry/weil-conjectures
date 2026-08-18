/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Blowup.Complement
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

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

- `AlgebraicGeometry.isIso_pullback_fst_strictTransformι`: the strict transform
  contains the whole open locus over `U`;
- `AlgebraicGeometry.isPullback_strictTransformOpen`: if `π` is an isomorphism over
  `U`, the open locus is canonically `Y ×_X U`;
- `AlgebraicGeometry.isPullback_strictTransform_over`: the combination of the previous
  two, identifying the part of the strict transform lying over `U` with the ordinary base
  change `Y ×_X U` (blueprint: `lemma:nagata-strict-transform-over-complement`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y X' : Scheme.{u}} (f : Y ⟶ X) (π : X' ⟶ X) (U : X.Opens)

/-- The open locus of the fibre product `Y ×_X X'` lying over the open `U ⊆ X`. -/
abbrev strictTransformOpen : (pullback f π).Opens :=
  pullback.snd f π ⁻¹ᵁ (π ⁻¹ᵁ U)

/-- The open locus over `U` is the preimage of `U` under the structure morphism of the
fibre product to the base. -/
lemma strictTransformOpen_eq_preimage :
    strictTransformOpen f π U = (pullback.fst f π ≫ f) ⁻¹ᵁ U := by
  rw [strictTransformOpen, ← Scheme.Hom.comp_preimage, pullback.condition]

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

/-- The ideal sheaf cutting out the strict transform is the kernel of the open locus. -/
lemma ker_strictTransformι :
    (strictTransformι f π U).ker = ((strictTransformOpen f π U).ι).ker :=
  Scheme.IdealSheafData.ker_subschemeι _

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

/-- **The strict transform over the preserved open**: combining
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

end PullbackComparison

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe v

variable {X : Scheme.{v}} (I : X.IdealSheafData) {Y : Scheme.{v}} (f : Y ⟶ X)

/-- The strict transform of `f : Y ⟶ X` along the blow-up of the ideal sheaf `I`,
preserving the complement of the support of `I`.
(Blueprint: `def:nagata-strict-transform`.) -/
def strictTransform : Scheme.{v} :=
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
