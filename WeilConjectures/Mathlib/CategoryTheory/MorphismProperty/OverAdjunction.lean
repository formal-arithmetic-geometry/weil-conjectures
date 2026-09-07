/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Fully faithfulness of `MorphismProperty.Over.map`, base change squares, and the
coherence of base change

The functor `MorphismProperty.Over.map` given by post-composition with a morphism
satisfying `P` is always faithful (`CategoryTheory.MorphismProperty.Over.faithful_map`),
and it is full when the morphism is a monomorphism
(`CategoryTheory.MorphismProperty.Over.full_map`).

Base change along a morphism `f : X ⟶ Y` sends a morphism of `P.Over Q Y` to a cartesian
square (`CategoryTheory.MorphismProperty.Over.isPullback_map_left`).

Finally, base change is a pseudofunctor: base change along the identity is the identity
functor, and the composition isomorphism `MorphismProperty.Over.pullbackComp` satisfies the
associativity pentagon and the two unit triangles.

## Main definitions

- `CategoryTheory.MorphismProperty.Over.pullbackId`: base change along `𝟙 X` is `𝟭`.

## Main results

- `CategoryTheory.MorphismProperty.Over.pullbackComp_inv_assoc` and
  `CategoryTheory.MorphismProperty.Over.pullbackComp_hom_assoc`: the associativity
  coherence of `MorphismProperty.Over.pullbackComp`.
- `CategoryTheory.MorphismProperty.Over.pullbackComp_id_right` and
  `CategoryTheory.MorphismProperty.Over.pullbackComp_id_left`: its unit coherence.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {T : Type*} [Category T] {P Q : MorphismProperty T} [Q.IsMultiplicative]
  {X Y : T}

section Map

variable [P.IsStableUnderComposition] {f : X ⟶ Y} (hPf : P f)

/-- The functor `MorphismProperty.Over.map` given by post-composition with `f` is always
faithful: it acts as the identity on the underlying morphisms. -/
instance MorphismProperty.Over.faithful_map : (MorphismProperty.Over.map Q hPf).Faithful where
  map_injective {A B} {φ ψ} h := by
    apply MorphismProperty.Over.Hom.ext
    have h' : ((MorphismProperty.Over.map Q hPf).map φ).left =
        ((MorphismProperty.Over.map Q hPf).map ψ).left := by rw [h]
    simpa using h'

/-- For a monomorphism `f`, the functor `MorphismProperty.Over.map` given by
post-composition with `f` is full: the compatibility with the structure morphisms over
the target can be cancelled along `f`. -/
instance MorphismProperty.Over.full_map [Mono f] : (MorphismProperty.Over.map Q hPf).Full where
  map_surjective {A B} ψ := by
    refine ⟨MorphismProperty.Over.homMk ψ.left ?_ ψ.prop_hom_left, ?_⟩
    · rw [← cancel_mono f]
      simpa using MorphismProperty.Over.w ψ
    · apply MorphismProperty.Over.Hom.ext
      simp

end Map

section Pullback

variable [Q.IsStableUnderBaseChange] (f : X ⟶ Y) [P.HasPullbacksAlong f]
  [P.IsStableUnderBaseChangeAlong f]

/-- Base change along `f : X ⟶ Y` sends a morphism `φ : A ⟶ B` of `P.Over Q Y` to a
cartesian square: it exhibits `A ×_Y X` as the fibre product of `A` and `B ×_Y X` over `B`.

```
  A ×_Y X ──(Over.pullback P Q f).map φ──→ B ×_Y X
     │                                        │
     │ pullback.fst A.hom f                   │ pullback.fst B.hom f
     ↓                                        ↓
     A ──────────────── φ.left ─────────────→ B
```
-/
lemma MorphismProperty.Over.isPullback_map_left {A B : P.Over Q Y} (φ : A ⟶ B) :
    IsPullback (pullback.fst A.hom f) ((MorphismProperty.Over.pullback P Q f).map φ).left φ.left
      (pullback.fst B.hom f) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback B.hom f)
  have h : ((MorphismProperty.Over.pullback P Q f).map φ).left ≫ pullback.snd B.hom f =
      pullback.snd A.hom f := by
    simp
  rw [h, MorphismProperty.Over.w φ]
  exact IsPullback.of_hasPullback A.hom f

end Pullback

section PullbackCoherence

variable [Q.IsStableUnderBaseChange] [Q.RespectsIso] [P.IsStableUnderBaseChange]
  [HasPullbacks T]

/-- Base change along the identity is the identity functor: the fibre product `A ×_X X` is
`A`, via the first projection. -/
noncomputable def MorphismProperty.Over.pullbackId (X : T) :
    MorphismProperty.Over.pullback P Q (𝟙 X) ≅ 𝟭 (P.Over Q X) :=
  NatIso.ofComponents
    (fun A ↦ MorphismProperty.Over.isoMk (asIso (pullback.fst A.hom (𝟙 X)))
      (by simpa using pullback.condition (f := A.hom) (g := 𝟙 X)))
    (fun {A B} φ ↦ by ext; simp)

/-- The associativity coherence of `MorphismProperty.Over.pullbackComp`: the two ways of
decomposing base change along a triple composite `f ≫ g ≫ h` agree. Stated for the
inverses; see `MorphismProperty.Over.pullbackComp_hom_assoc` for the version for the
underlying isomorphisms. -/
lemma MorphismProperty.Over.pullbackComp_inv_assoc {X Y Z W : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (gh : Y ⟶ W) (hgh : gh = g ≫ h)
    (fgh : X ⟶ W) (hfgh : fgh = fg ≫ h) (hfgh' : fgh = f ≫ gh) :
    Functor.whiskerLeft (MorphismProperty.Over.pullback P Q h)
        (MorphismProperty.Over.pullbackComp f g fg hfg).inv ≫
      (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) fg h fgh hfgh).inv =
    (Functor.associator (MorphismProperty.Over.pullback P Q h)
          (MorphismProperty.Over.pullback P Q g) (MorphismProperty.Over.pullback P Q f)).inv ≫
      Functor.whiskerRight (MorphismProperty.Over.pullbackComp g h gh hgh).inv
        (MorphismProperty.Over.pullback P Q f) ≫
      (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f gh fgh hfgh').inv := by
  ext A
  apply pullback.hom_ext <;>
    simp [pullback.map, MorphismProperty.Over.pullback, MorphismProperty.Over.mk]

/-- Unit coherence of `MorphismProperty.Over.pullbackComp`: composing with the identity on
the target. -/
lemma MorphismProperty.Over.pullbackComp_id_right {X Y : T} (f : X ⟶ Y) :
    (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f (𝟙 Y) f (by simp)).hom =
      (MorphismProperty.Over.pullback P Q f).leftUnitor.inv ≫
        Functor.whiskerRight (MorphismProperty.Over.pullbackId (P := P) (Q := Q) Y).inv
          (MorphismProperty.Over.pullback P Q f) := by
  ext A
  apply pullback.hom_ext <;>
    simp [pullback.map, MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackId]

/-- Unit coherence of `MorphismProperty.Over.pullbackComp`: composing with the identity on
the source. -/
lemma MorphismProperty.Over.pullbackComp_id_left {X Z : T} (g : X ⟶ Z) :
    (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) (𝟙 X) g g (by simp)).hom =
      (MorphismProperty.Over.pullback P Q g).rightUnitor.inv ≫
        Functor.whiskerLeft (MorphismProperty.Over.pullback P Q g)
          (MorphismProperty.Over.pullbackId (P := P) (Q := Q) X).inv := by
  ext A
  apply pullback.hom_ext
  · simp only [pullback, Functor.id_obj, Functor.const_obj_obj, Over.mk, Functor.comp_obj,
      pullbackComp_hom_app_left, pullback.map, comp_id, assoc, pullbackId, NatTrans.comp_app,
      Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, NatIso.ofComponents_inv_app,
      id_comp, isoMk_inv_left, asIso_inv, IsIso.inv_hom_id]
    apply pullback.hom_ext <;> simp
  · simp [pullback.map, MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackId]

/-- The associativity coherence of `MorphismProperty.Over.pullbackComp`, for the
isomorphisms themselves; see `MorphismProperty.Over.pullbackComp_inv_assoc`. -/
lemma MorphismProperty.Over.pullbackComp_hom_assoc {X Y Z W : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (gh : Y ⟶ W) (hgh : gh = g ≫ h)
    (fgh : X ⟶ W) (hfgh : fgh = fg ≫ h) (hfgh' : fgh = f ≫ gh) :
    (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (MorphismProperty.Over.pullback P Q h)
          (MorphismProperty.Over.pullbackComp f g fg hfg).hom =
      (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f gh fgh hfgh').hom ≫
        Functor.whiskerRight (MorphismProperty.Over.pullbackComp g h gh hgh).hom
          (MorphismProperty.Over.pullback P Q f) ≫
        (Functor.associator (MorphismProperty.Over.pullback P Q h)
          (MorphismProperty.Over.pullback P Q g) (MorphismProperty.Over.pullback P Q f)).hom := by
  have key : MorphismProperty.Over.pullbackComp (P := P) (Q := Q) fg h fgh hfgh ≪≫
        Functor.isoWhiskerLeft (MorphismProperty.Over.pullback P Q h)
          (MorphismProperty.Over.pullbackComp f g fg hfg) =
      MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f gh fgh hfgh' ≪≫
        Functor.isoWhiskerRight (MorphismProperty.Over.pullbackComp g h gh hgh)
            (MorphismProperty.Over.pullback P Q f) ≪≫
          Functor.associator (MorphismProperty.Over.pullback P Q h)
            (MorphismProperty.Over.pullback P Q g) (MorphismProperty.Over.pullback P Q f) :=
    Iso.ext ((Iso.inv_eq_inv _ _).mp (by
      simpa using MorphismProperty.Over.pullbackComp_inv_assoc (P := P) (Q := Q) f g h fg hfg
        gh hgh fgh hfgh hfgh'))
  simpa using congrArg Iso.hom key

end PullbackCoherence

end CategoryTheory
