/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Geometry of the base-changed scheme limit

Source: Stacks Project Tag 09Z1; Mathlib `AffineTransitionLimit`.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale

/-- Base change of a qcqs inverse system over an affine scheme satisfies the
geometric hypotheses for continuity of higher direct images.

Source: Stacks Project Tag 09Z1 (base-changed inverse systems), and Mathlib
`AffineTransitionLimit`, lemma `isAffineHom_π_app`. -/
theorem baseChange_target_limit_geometry {X S T : Scheme.{u}} [IsAffine S]
    (p : X ⟶ S) (g : T ⟶ S) {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over T)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Cone D) (hc : IsLimit ((Over.forget T).mapCone c)) :
    let B := Over.pullback (pullback.fst g p)
    (∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ B).map f).left) ∧
    (∀ i, QuasiCompact (((D ⋙ B).obj i).hom ≫ pullback.snd g p)) ∧
    (∀ i, QuasiSeparated (((D ⋙ B).obj i).hom ≫ pullback.snd g p)) ∧
    QuasiCompact ((B.mapCone c).pt.hom ≫ pullback.snd g p) ∧
    QuasiSeparated ((B.mapCone c).pt.hom ≫ pullback.snd g p) ∧
    Nonempty (IsLimit ((Over.forget (pullback g p)).mapCone (B.mapCone c)))  := by
  let B := Over.pullback (pullback.fst g p)
  have sq (U : Over T) : IsPullback (pullback.fst U.hom (pullback.fst g p))
      ((B.obj U).hom ≫ pullback.snd g p) (U.hom ≫ g) p :=
    (IsPullback.of_hasPullback U.hom (pullback.fst g p)).paste_vert
      (IsPullback.of_hasPullback g p)
  have hqc (U : Over T) [QuasiCompact (U.hom ≫ g)] :
      QuasiCompact ((B.obj U).hom ≫ pullback.snd g p) :=
    MorphismProperty.of_isPullback (sq U) inferInstance
  have hqs (U : Over T) [QuasiSeparated (U.hom ≫ g)] :
      QuasiSeparated ((B.obj U).hom ≫ pullback.snd g p) :=
    MorphismProperty.of_isPullback (sq U) inferInstance
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have : IsConnected I := IsCofiltered.isConnected I
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ Over.forget T).map f) :=
    fun _ ↦ inferInstanceAs (IsAffineHom (D.map _).left)
  have : IsAffineHom (c.π.app i).left :=
    isAffineHom_π_app (D ⋙ Over.forget T) ((Over.forget T).mapCone c) hc i
  have hw : c.pt.hom ≫ g = (c.π.app i).left ≫ ((D.obj i).hom ≫ g) := by
    rw [← Category.assoc, Over.w]
    rfl
  have : QuasiCompact (c.pt.hom ≫ g) := by rw [hw]; infer_instance
  have : QuasiSeparated (c.pt.hom ≫ g) := by rw [hw]; infer_instance
  refine ⟨?_, (fun i ↦ hqc (D.obj i)), (fun i ↦ hqs (D.obj i)),
    hqc c.pt, hqs c.pt, ?_⟩
  · intro i j f
    exact MorphismProperty.overPullbackMap _ _ inferInstance
  · exact ⟨isLimitOfPreserves (Over.forget (pullback g p))
      (isLimitOfPreserves B (isLimitOfReflects (Over.forget T) hc))⟩


end AlgebraicGeometry.Etale
