/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Closed immersions of base-changed diagonals

## References

* [Stacks, Tag 01ZQ]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
/-- Base change of the diagonal over the original base detects separatedness of the
base-changed morphism (Stacks, Tag 01ZQ). -/
theorem isClosedImmersion_overPullback_diagonal_iff
    {S T : Scheme.{u}} (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    IsClosedImmersion
        (((Over.pullback g).map
          (Over.homMk (pullback.diagonal f.left) (by simp) :
            X ⟶ Over.mk (pullback.snd f.left f.left ≫ X.hom))).left) ↔
      IsSeparated (((Over.pullback g).map f).left) := by
  let f' := ((Over.pullback g).map f).left
  let Z := Over.mk (pullback.snd f.left f.left ≫ X.hom)
  let γ : X ⟶ Z := Over.homMk (pullback.diagonal f.left) (by simp [Z])
  let a : pullback Z.hom g ⟶ pullback X.hom g :=
    pullback.lift (pullback.fst Z.hom g ≫ pullback.fst f.left f.left)
      (pullback.snd Z.hom g) (by
        rw [Category.assoc, ← Over.w f]
        rw [pullback.condition_assoc]
        simpa [Z, Category.assoc, Over.w f] using (pullback.condition (f := Z.hom) (g := g)))
  let b : pullback Z.hom g ⟶ pullback X.hom g :=
    pullback.lift (pullback.fst Z.hom g ≫ pullback.snd f.left f.left)
      (pullback.snd Z.hom g) (by
        simpa [Z, Category.assoc] using (pullback.condition (f := Z.hom) (g := g)))
  have hab : a ≫ f' = b ≫ f' := by
    apply pullback.hom_ext
    · simp [a, b, f', Over.pullback, pullback.condition]
    · simp [a, b, f', Over.pullback]
  let e : pullback Z.hom g ⟶ pullback f' f' := pullback.lift a b hab
  let d : pullback f' f' ⟶ pullback f.left f.left :=
    pullback.lift (pullback.fst f' f' ≫ pullback.fst X.hom g)
      (pullback.snd f' f' ≫ pullback.fst X.hom g) (by
        have h := congrArg (fun k ↦ k ≫ pullback.fst Y.hom g)
          (pullback.condition (f := f') (g := f'))
        simpa [f', Over.pullback] using h)
  have ht : pullback.fst f' f' ≫ pullback.snd X.hom g =
      pullback.snd f' f' ≫ pullback.snd X.hom g := by
    have h := congrArg (fun k ↦ k ≫ pullback.snd Y.hom g) (pullback.condition (f := f') (g := f'))
    simpa [f', Over.pullback] using h
  let v : pullback f' f' ⟶ pullback Z.hom g :=
    pullback.lift d (pullback.snd f' f' ≫ pullback.snd X.hom g) (by
      simp [d, Z, pullback.condition])
  have hev : e ≫ v = 𝟙 _ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [e, v, d, a, b]
    · simp [e, v, b]
  have hve : v ≫ e = 𝟙 _ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [e, v, a, d]
      · simpa [e, v, a] using ht.symm
    · apply pullback.hom_ext <;> simp [e, v, b, d]
  let E : pullback Z.hom g ≅ pullback f' f' := ⟨e, v, hev, hve⟩
  have heγ : ((Over.pullback g).map γ).left ≫ E.hom = pullback.diagonal f' := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [E, e, a, b, γ, Over.pullback]
  change IsClosedImmersion (((Over.pullback g).map γ).left) ↔ IsSeparated f'
  rw [show IsSeparated f' ↔ IsClosedImmersion (pullback.diagonal f') from
    ⟨fun h ↦ h.isClosedImmersion_diagonal, fun h ↦ ⟨h⟩⟩]
  have : IsIso E.hom := ⟨⟨E.inv, E.hom_inv_id, E.inv_hom_id⟩⟩
  rw [← heγ]
  exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).symm

end AlgebraicGeometry
