/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!

# Base change of an open immersion in a fibre product

For `j : U ⟶ X` and morphisms `x : X ⟶ S`, `y : Y ⟶ S`, the induced morphism
`U ×_S Y ⟶ X ×_S Y` is a base change of `j` along the first projection. In the
application `j` is an admissible blow-up and `U ×_S Y ⟶ X ×_S Y` is the locus over
which a partial section of the first projection is defined.

## Main definitions and results

- `AlgebraicGeometry.partialSectionOpenι`: the base-changed morphism `U ×_S Y ⟶ X ×_S Y`;
- `AlgebraicGeometry.isPullback_partialSectionOpenι`: it is a base change of `j`;
- `AlgebraicGeometry.isIso_partialSectionOpenι_restrict`: hence, if `j` restricts to an
  isomorphism over an open `V ⊆ X`, then `U ×_S Y ⟶ X ×_S Y` restricts to an
  isomorphism over the preimage of `V`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {S X Y U : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (j : U ⟶ X)

/-- The base-changed morphism `U ×_S Y ⟶ X ×_S Y` induced by `j : U ⟶ X`. -/
def partialSectionOpenι : pullback (j ≫ x) y ⟶ pullback x y :=
  pullback.map (j ≫ x) y x y j (𝟙 Y) (𝟙 S) rfl (by simp)

@[reassoc (attr := simp)]
lemma partialSectionOpenι_fst :
    partialSectionOpenι x y j ≫ pullback.fst x y = pullback.fst (j ≫ x) y ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma partialSectionOpenι_snd :
    partialSectionOpenι x y j ≫ pullback.snd x y = pullback.snd (j ≫ x) y :=
  pullback.lift_snd _ _ _

instance [IsOpenImmersion j] : IsOpenImmersion (partialSectionOpenι x y j) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› inferInstance rfl (by simp)

instance [QuasiCompact j] : QuasiCompact (partialSectionOpenι x y j) :=
  MorphismProperty.pullbackMap (P := @QuasiCompact) ‹_› inferInstance rfl (by simp)

/-- **The base-changed square is cartesian**: `U ×_S Y` is the fibre product of
`j : U ⟶ X` and the first projection `X ×_S Y ⟶ X`. -/
lemma isPullback_partialSectionOpenι :
    IsPullback (partialSectionOpenι x y j) (pullback.fst (j ≫ x) y)
      (pullback.fst x y) j :=
  IsPullback.of_right (by simpa using (IsPullback.of_hasPullback (j ≫ x) y).flip)
    (partialSectionOpenι_fst x y j) (IsPullback.of_hasPullback x y).flip

/-- **The base change of an isomorphism over an open stays an isomorphism**: if
`j : U ⟶ X` restricts to an isomorphism over an open `V ⊆ X` — in the application `j`
is an admissible blow-up and `V` the complement of its center — then the base-changed
morphism `U ×_S Y ⟶ X ×_S Y` restricts to an isomorphism over the preimage of `V`
under the first projection. -/
lemma isIso_partialSectionOpenι_restrict (V : X.Opens) [IsIso (j ∣_ V)] :
    IsIso (partialSectionOpenι x y j ∣_ (pullback.fst x y ⁻¹ᵁ V)) := by
  -- `(U ×_S Y)|_{ρ⁻¹V}` is `U ×_X (X ×_S Y)|_V` by pasting the restriction square onto
  -- the cartesian square above, ...
  have hA : IsPullback (partialSectionOpenι x y j ∣_ (pullback.fst x y ⁻¹ᵁ V))
      (partialSectionOpenι x y j ⁻¹ᵁ (pullback.fst x y ⁻¹ᵁ V)).ι
      (pullback.fst x y ⁻¹ᵁ V).ι (partialSectionOpenι x y j) :=
    isPullback_morphismRestrict _ _
  have hpaste := hA.paste_vert (isPullback_partialSectionOpenι x y j)
  -- ... and `(X ×_S Y)|_V ⟶ X` factors through `V`, so it is `j|_V` base-changed.
  have ht : IsPullback (j ⁻¹ᵁ V).ι (j ∣_ V) j V.ι :=
    (isPullback_morphismRestrict j V).flip
  have hs : IsPullback ((partialSectionOpenι x y j ⁻¹ᵁ (pullback.fst x y ⁻¹ᵁ V)).ι ≫
        pullback.fst (j ≫ x) y)
      (partialSectionOpenι x y j ∣_ (pullback.fst x y ⁻¹ᵁ V)) j
      ((pullback.fst x y ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι]
    exact hpaste.flip
  exact (IsPullback.of_right' hs ht).flip.isIso_fst_of_isIso

end AlgebraicGeometry
