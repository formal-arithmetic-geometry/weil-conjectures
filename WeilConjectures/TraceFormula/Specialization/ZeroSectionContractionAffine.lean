/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ZeroSectionContraction
public import WeilConjectures.TraceFormula.Specialization.ZeroSectionAffine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!

# The contraction of affine space onto a coordinate hyperplane

The linear projection `H_0 : 𝔸ⁿ⁺¹_k ⟶ 𝔸ⁿ⁺¹_k`, `(v, x) ↦ (v, 0)`, the value at `a = 0` of the
scaling `H_a(v, x) = (v, a x)` of Verdier's contraction argument (blueprint
`det-sp-thick-origin-homotopy`), factors through the coordinate hyperplane `Z = 𝔸ⁿ × {0}` as a
retraction `r : 𝔸ⁿ⁺¹_k ⟶ Z` of the inclusion
(`ProEtale.CondensedRing.coordinateHyperplaneRetraction`). Consequently the zero-section map of
`(𝔸ⁿ⁺¹_k, Z)` at a complex `Lr^* M` pulled back from the hyperplane is a split epimorphism, and
its defect vanishes if and only if `Le^*` of the pullback exchange of the lift `r̃` is an
isomorphism
(`ProEtale.CondensedRing.isZero_specializationDefect_coordinateHyperplaneRetraction_iff`).

## What is missing for the full contraction argument

Verdier's argument shows `Le^*(α_r(M))` invertible by comparing it with the value at `a = 1` of the
family of endomorphisms `φ_a` induced by the scaling `H : 𝔸ⁿ⁺¹ × 𝔸¹ ⟶ 𝔸ⁿ⁺¹`. This requires
`𝔸¹`-homotopy invariance on the special fibre (full faithfulness of the pullback along
`Z_{k'} × 𝔸¹ ⟶ Z_{k'}` on the pro-étale derived category), which is not available. The argument only
applies to complexes `L` with `H^* L ≅ pr^* L`, that is (restricting to `a = 0`) `L ≅ Lr^* Li^* L`:
exactly the complexes `Lr^* M` treated here.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (k : Type u) [Field k] (n : ℕ)

/-- The coordinates of the linear projection `(v, x) ↦ (v, 0)` of `𝔸ⁿ⁺¹_k`. -/
noncomputable def coordinateHyperplaneProjVector :
    ULift.{u} (Fin (n + 1)) → Γ((affineSpaceOver k n).left, ⊤) :=
  fun j ↦ if j.down = Fin.last n then 0 else AffineSpace.coord (Spec (.of k)) j

/-- The linear projection `H_0 : 𝔸ⁿ⁺¹_k ⟶ 𝔸ⁿ⁺¹_k`, `(v, x) ↦ (v, 0)`. -/
noncomputable def coordinateHyperplaneProj : affineSpaceOver k n ⟶ affineSpaceOver k n :=
  Over.homMk (AffineSpace.homOfVector (affineSpaceOver k n).hom
    (coordinateHyperplaneProjVector k n)) (AffineSpace.homOfVector_over _ _)

lemma coordinateHyperplaneProj_left :
    (coordinateHyperplaneProj k n).left = AffineSpace.homOfVector (affineSpaceOver k n).hom
      (coordinateHyperplaneProjVector k n) :=
  rfl

lemma coordinateHyperplane_le_ker_coordinateHyperplaneProj :
    (coordinateHyperplane k n).subschemeι.ker ≤ (coordinateHyperplaneProj k n).left.ker := by
  rw [IdealSheafData.ker_subschemeι]
  refine IdealSheafData.ofIdealTop_span_le_ker _ fun t ht ↦ ?_
  rw [Set.mem_singleton_iff.mp ht, coordinateHyperplaneProj_left]
  exact (AffineSpace.homOfVector_appTop_coord _ _ _).trans (if_pos rfl)

/-- The retraction `r : 𝔸ⁿ⁺¹_k ⟶ 𝔸ⁿ × {0}` of the inclusion of the coordinate hyperplane: the
linear projection `(v, x) ↦ (v, 0)`, corestricted to the hyperplane. -/
noncomputable def coordinateHyperplaneRetraction :
    affineSpaceOver k n ⟶ centre (affineSpaceOver k n) (coordinateHyperplane k n) :=
  Over.homMk (IsClosedImmersion.lift (coordinateHyperplane k n).subschemeι
    (coordinateHyperplaneProj k n).left (coordinateHyperplane_le_ker_coordinateHyperplaneProj k n))
    ((IsClosedImmersion.lift_fac_assoc _ _ _ (affineSpaceOver k n).hom).trans
      (Over.w (coordinateHyperplaneProj k n)))

@[reassoc]
lemma coordinateHyperplaneRetraction_left_centreι_left :
    (coordinateHyperplaneRetraction k n).left ≫ (centreι _ _).left =
      (coordinateHyperplaneProj k n).left :=
  IsClosedImmersion.lift_fac _ _ _

/-- The linear projection `(v, x) ↦ (v, 0)` is the identity on the coordinate hyperplane. -/
lemma centreι_left_coordinateHyperplaneProj_left :
    (centreι (affineSpaceOver k n) (coordinateHyperplane k n)).left ≫
      (coordinateHyperplaneProj k n).left =
      (centreι (affineSpaceOver k n) (coordinateHyperplane k n)).left := by
  refine AffineSpace.hom_ext ?_ fun j ↦ ?_
  · rw [Category.assoc, coordinateHyperplaneProj_left, AffineSpace.homOfVector_over]
    rfl
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordinateHyperplaneProj_left,
      AffineSpace.homOfVector_appTop_coord, coordinateHyperplaneProjVector]
    split_ifs with hj
    · obtain rfl : j = ULift.up (Fin.last n) := ULift.ext _ _ hj
      rw [map_zero, centreι_left]
      refine (IdealSheafData.subschemeι_appTop_eq_zero _ _ fun U ↦ ?_).symm
      rw [coordinateHyperplane, IdealSheafData.ofIdealTop_ideal]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)
    · rfl

/-- `r : 𝔸ⁿ⁺¹_k ⟶ 𝔸ⁿ × {0}` is a retraction of the inclusion of the coordinate hyperplane. -/
lemma centreι_coordinateHyperplaneRetraction :
    centreι _ _ ≫ coordinateHyperplaneRetraction k n = 𝟙 _ := by
  ext1
  rw [Over.comp_left, Over.id_left, ← cancel_mono (centreι _ _).left, Category.assoc,
    coordinateHyperplaneRetraction_left_centreι_left, centreι_left_coordinateHyperplaneProj_left,
    Category.id_comp]

variable {k} (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The zero-section map of `(𝔸ⁿ⁺¹_k, 𝔸ⁿ × 0)` at a complex `Lr^* M` pulled back from the
coordinate hyperplane along the linear projection is a split epimorphism. -/
theorem isSplitEpi_zeroSectionMap_coordinateHyperplaneRetraction
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (centre (affineSpaceOver k n) (coordinateHyperplane k n)).left) Ab.{u + 1})
      (condensedRingObj Λ (centre (affineSpaceOver k n) (coordinateHyperplane k n)).left))) :
    IsSplitEpi (zeroSectionMap (affineSpaceOver k n) (coordinateHyperplane k n) k' Λ
      (L(((coordinateHyperplaneRetraction k n).left)^*⟦Λ⟧).obj M)) :=
  isSplitEpi_zeroSectionMap_upperStar_retraction _ _ k' Λ
    (centreι_coordinateHyperplaneRetraction k n) M

/-- **Contraction onto a coordinate hyperplane** (blueprint `det-sp-thick-origin-homotopy`, the
case of complexes pulled back from the hyperplane): the defect `C_{𝔸ⁿ⁺¹, 𝔸ⁿ × 0}(Lr^* M)` of a
complex pulled back along the linear projection `r` vanishes if and only if `Le^*` of the pullback
exchange `α_r(M)` of the lift `r̃ : 𝒟 ⟶ (𝔸ⁿ × 0) × S` is an isomorphism. -/
theorem isZero_specializationDefect_coordinateHyperplaneRetraction_iff
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (centre (affineSpaceOver k n) (coordinateHyperplane k n)).left) Ab.{u + 1})
      (condensedRingObj Λ (centre (affineSpaceOver k n) (coordinateHyperplane k n)).left))) :
    IsZero (specializationDefect (affineSpaceOver k n) (coordinateHyperplane k n) k' Λ
        (L(((coordinateHyperplaneRetraction k n).left)^*⟦Λ⟧).obj M)) ↔
      IsIso (L(((zeroSectionSpecialFibreMap (affineSpaceOver k n) (coordinateHyperplane k n)
        k').left)^*⟦Λ⟧).map
          (((retractionModelHom _ _ k' (coordinateHyperplaneRetraction k n)).pullbackExchange
            Λ).app M)) :=
  (isZero_specializationDefect_iff _ _ k' Λ _).trans
    (isIso_zeroSectionMap_upperStar_retraction_iff _ _ k' Λ
      (centreι_coordinateHyperplaneRetraction k n) M)

end AlgebraicGeometry.ProEtale.CondensedRing
