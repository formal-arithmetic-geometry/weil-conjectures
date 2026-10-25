/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ZeroSectionAffine
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!

# The defect of a complex pulled back from the affine line

The projection `𝔸ⁿ⁺¹_k ⟶ 𝔸¹_k` onto the last coordinate
(`ProEtale.CondensedRing.affineSpaceLastCoord`) is smooth, and the coordinate hyperplane
`𝔸ⁿ × {0}` is the schematic inverse image of the origin `{0} ⊆ 𝔸¹_k`
(`ProEtale.CondensedRing.comap_affineSpaceLastCoord_coordinateHyperplane`). By smooth exchange for
the defect, the defect `C_{𝔸ⁿ⁺¹, 𝔸ⁿ × 0}` of a complex pulled back from the line vanishes as soon
as the defect `C_{𝔸¹, 0}` of the complex on the line does
(`ProEtale.CondensedRing.isZero_specializationDefect_affineSpace_upperStar_of_isZero`; a case of
blueprint `det-sp-zero-section-affine-space`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (k : Type u) [Field k]

/-- The projection `𝔸ⁿ⁺¹_k ⟶ 𝔸¹_k` onto the last coordinate. -/
noncomputable def affineSpaceLastCoord (n : ℕ) : affineSpaceOver k n ⟶ affineSpaceOver k 0 :=
  Over.homMk (AffineSpace.homOfVector (affineSpaceOver k n).hom
    fun _ ↦ AffineSpace.coord (Spec (.of k)) (ULift.up (Fin.last n)))
    (AffineSpace.homOfVector_over _ _)

lemma affineSpaceLastCoord_left (n : ℕ) :
    (affineSpaceLastCoord k n).left = AffineSpace.homOfVector (affineSpaceOver k n).hom
      fun _ ↦ AffineSpace.coord (Spec (.of k)) (ULift.up (Fin.last n)) :=
  rfl

/-- The splitting `𝔸¹ ⊕ 𝔸ⁿ` of the coordinates of `𝔸ⁿ⁺¹`, the first summand being the last
coordinate. -/
def affineSpaceLastCoordEquiv (n : ℕ) :
    ULift.{u} (Fin 1) ⊕ ULift.{u} (Fin n) ≃ ULift.{u} (Fin (n + 1)) :=
  (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
    ((Equiv.sumComm _ _).trans (finSumFinEquiv.trans Equiv.ulift.symm))

/-- The projection onto the last coordinate is, up to relabelling the coordinates, the projection
`𝔸ⁿ(𝔸¹_k) ⟶ 𝔸¹_k`. -/
lemma affineSpaceLastCoord_left_eq (n : ℕ) :
    (affineSpaceLastCoord k n).left =
      (AffineSpace.reindexIso (Spec (.of k)) (affineSpaceLastCoordEquiv n)).hom ≫
        (AffineSpace.sumIso (Spec (.of k))).hom ≫
          𝔸(ULift.{u} (Fin n); 𝔸(ULift.{u} (Fin 1); Spec (.of k))) ↘
            𝔸(ULift.{u} (Fin 1); Spec (.of k)) := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, Category.assoc, AffineSpace.sumIso_hom_over_over,
      AffineSpace.reindexIso_hom, AffineSpace.reindex_over, affineSpaceLastCoord_left]
    exact AffineSpace.homOfVector_over _ _
  · rw [AffineSpace.sumIso_hom, AffineSpace.sumHom_over, AffineSpace.reindexIso_hom,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord,
      Function.comp_apply]
    refine ((AffineSpace.homOfVector_appTop_coord _ _ _).trans ?_).trans
      (AffineSpace.reindex_appTop_coord _ _ _).symm
    congr 1
    ext
    simp [affineSpaceLastCoordEquiv, Fin.fin_one_eq_zero i.down]

instance (n : ℕ) : Smooth (affineSpaceLastCoord k n).left := by
  rw [affineSpaceLastCoord_left_eq, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth),
    MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)]
  have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n))
    𝔸(ULift.{u} (Fin 1); Spec (.of k))
  exact SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin n))) _

/-- The coordinate hyperplane `𝔸ⁿ × {0} ⊆ 𝔸ⁿ⁺¹_k` is the inverse image of the origin of `𝔸¹_k`
under the projection onto the last coordinate. -/
lemma comap_affineSpaceLastCoord_coordinateHyperplane (n : ℕ) :
    (coordinateHyperplane k 0).comap (affineSpaceLastCoord k n).left =
      coordinateHyperplane k n := by
  refine IdealSheafData.ext_of_isAffine ?_
  rw [IdealSheafData.ideal_top_comap_of_isAffine, coordinateHyperplane, coordinateHyperplane,
    IdealSheafData.ideal_top_ofIdealTop, IdealSheafData.ideal_top_ofIdealTop, Ideal.map_span,
    Set.image_singleton]
  congr 2
  exact AffineSpace.homOfVector_appTop_coord _ _ _

variable {k} {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **The defect of a complex pulled back from the line** (a case of blueprint
`det-sp-zero-section-affine-space`): if `M` is a bounded constructible complex on `𝔸¹_k` whose
defect `C_{𝔸¹, 0}(M)` vanishes, then the defect `C_{𝔸ⁿ⁺¹, 𝔸ⁿ × 0}(Lp^* M)` of its pullback along
the projection `p : 𝔸ⁿ⁺¹_k ⟶ 𝔸¹_k` onto the last coordinate vanishes. This is smooth exchange for
the defect, as `p` is smooth and `p⁻¹(0) = 𝔸ⁿ × 0`. -/
theorem isZero_specializationDefect_affineSpace_upperStar_of_isZero (n : ℕ)
    (M : Dᵇc((affineSpaceOver k 0).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : IsZero (specializationDefect (affineSpaceOver k 0) (coordinateHyperplane k 0) k'
      (Profinite.padicAlgClRingObj ℓ) M.obj)) :
    IsZero (specializationDefect (affineSpaceOver k n) (coordinateHyperplane k n) k'
      (Profinite.padicAlgClRingObj ℓ)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (affineSpaceLastCoord k n)).obj M).obj) := by
  have e := (nonempty_specializationDefect_upperStar_iso (affineSpaceLastCoord k n)
    (coordinateHyperplane k 0) k' M).some
  have h := (L(((centreSpecialFibreMap (affineSpaceLastCoord k n) (coordinateHyperplane k 0)
    k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_isZero hM).of_iso e
  exact comap_affineSpaceLastCoord_coordinateHyperplane k n ▸ h

end AlgebraicGeometry.ProEtale.CondensedRing
