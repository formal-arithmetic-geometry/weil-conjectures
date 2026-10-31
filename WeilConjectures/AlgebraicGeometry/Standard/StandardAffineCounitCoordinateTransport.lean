/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows

/-! Transport of the tower mate through affine coordinates.
Source: sk-thm-dnc, local construction, standard affine model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open SectionLocalDualizingComparisons

/-- Coordinate and Tate transport carries a tower mate square to affine space.
Source: sk-thm-dnc, local construction, standard affine model
(blueprint: lem-trf-standard-affine-counit-coordinate-transport).

Proof (steps 4, 6-8 of lem-trf-standard-affine-counit-base-change). Write `w` for the
tower map, `k_X = (affineTraceAffineSpaceIso X d).inv`, `u_X = towerTateIso X` and
`b` for the right base change at the unit followed by `R_T` of the unit pullback.
(i) The restricted-chart coefficient-core theorem, the ordered Tate regrouping
pullback and the composition compatibility of the canonical shifted Tate pullbacks
around `p_S w = v p_T` give `Lw^*(u_S⁻¹) ≫ b = τ_{w,d} ≫ u_T⁻¹`; with `hq` this is
`Lw^*(u_S⁻¹ ≫ qS) ≫ B_w = τ_{w,d} ≫ u_T⁻¹ ≫ qT`.
(ii) By `hsquare`, `k_T ≫ w = v_d ≫ k_S`; mate pasting for the two composites of
Cartesian squares (compact-support pasting identifies their left squares) gives
`v_d^* B_{k_S} ≫ B_{v_d} = ξ ≫ k_T^* B_w ≫ B_{k_T}` with `ξ` the inverse-image
compositor at the dualizing complex.
(iii) Expand the left side, apply (ii), compositor naturality and (i); the
root-normalized Tate pullbacks compose around `k_T w = v_d k_S`
(`sectionTatePullback_coherence`), identifying the first three factors with
`τ_{v_d,d} ≫ τ_{k_T,d}⁻¹`. The remaining factors are the right side. The morphisms
`qS`, `qT` enter only through `hq`.
-/
theorem standardAffineCounit_coordinateTransport (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (v : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (qS : (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ⟶
      dualizingComplex A (affineTraceProjection S d))
    (qT : (affineTraceRight A N hA T d).obj (ordinaryFiniteUnit A T) ⟶
      dualizingComplex A (affineTraceProjection T d))
    (hsquare : affineTraceMap v d ≫ (affineTraceAffineSpaceIso S d).hom =
      (affineTraceAffineSpaceIso T d).hom ≫
        AffineSpace.map (ULift.{u} (Fin d)) v)
    (hq : (ordinaryFinitePullback A (affineTraceMap v d)).map qS ≫
        dualizingComplexBaseChangeMap A (affineTraceMap_isPullback v d) =
      (affineTraceRightBaseChange A N hA t v hS d
          (ordinaryFiniteUnit A S)).hom ≫
        (affineTraceRight A N hA T d).map
          (ordinaryFiniteUnitPullback A v).hom ≫ qT) :
    (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin d)) v)).leftDerivedFunctor.map
        ((tatePullback A N hN hA (affineTraceAffineSpaceIso S d).inv
          (affineTraceInvertible N S hS d)
          (invertibleOnSource N (AffineSpace (ULift.{u} (Fin d)) S ↘ S) hS) d).inv ≫
          (ordinaryFinitePullback A (affineTraceAffineSpaceIso S d).inv).map
            ((CoordinateCounitArrows.towerTateIso A N hN hA t S hS d).inv ≫ qS)) ≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin d)) v)).leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A (CoordinateCounitArrows.standardSquare S d)) ≫
      dualizingComplexBaseChangeMap A (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) v) =
    (tatePullback A N hN hA (AffineSpace.map (ULift.{u} (Fin d)) v)
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin d)) S ↘ S) hS)
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin d)) T ↘ T)
        (invertibleOnSource N v hS)) d).hom ≫
      (tatePullback A N hN hA (affineTraceAffineSpaceIso T d).inv
        (affineTraceInvertible N T (invertibleOnSource N v hS) d)
        (invertibleOnSource N (AffineSpace (ULift.{u} (Fin d)) T ↘ T)
          (invertibleOnSource N v hS)) d).inv ≫
      (ordinaryFinitePullback A (affineTraceAffineSpaceIso T d).inv).map
        ((CoordinateCounitArrows.towerTateIso A N hN hA t T
          (invertibleOnSource N v hS) d).inv ≫ qT) ≫
      dualizingComplexBaseChangeMap A (CoordinateCounitArrows.standardSquare T d) := by
  sorry

end AlgebraicGeometry.Etale
