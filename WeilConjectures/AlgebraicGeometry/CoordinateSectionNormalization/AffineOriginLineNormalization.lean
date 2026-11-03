/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionOrdinary
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness
import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
import all WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.CoordinateSectionProjectiveTrace
import all WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.CoordinateSectionTensorTrace

/-! # Ordinary coordinate-line normalization for arbitrary finite coefficients

Source: current blueprint `det-sp-trace-basic`, Proof (2), the rank-one calculation
before the ordered coordinate induction (blueprint: lem-sp-affine-origin-line-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization

/-- The positive ordinary Cartier class integrates to one over any Noetherian base,
for every positive invertible annihilator of an arbitrary finite coefficient ring.

Source: current blueprint `det-sp-trace-basic`, Proof (2), rank-one subcalculation
(blueprint: lem-sp-affine-origin-line-normalization).

Proof: the projective zero section is closed since its composite with the separated
projective projection is identity. The coordinate-section chart computation identifies
its dual ideal with O(1). The supported Kummer Chern equation therefore identifies its
forget-supports morphism with the normalized projective Chern class. The canonical open
counit and identity-normalized compact-support composition identify the affine supported
source with the projective source. Apply the proved projective trace equation to obtain
identity. The proof works over nonreduced and empty bases, and for the zero ring.
-/
theorem affineOriginLine_scalar
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible) :
    (sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
      (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _ := by
  have hz : projectiveZero T ≫ (ProjectiveLine T ↘ T) = 𝟙 T := by
    rw [projectiveZero, Category.assoc, ProjectiveLine.affineChart_over]
    exact AffineSpace.zeroSection_comp_over PUnit.{u + 1} T
  let : IsClosedImmersion (projectiveZero T) := by
    have : IsClosedImmersion (projectiveZero T ≫ (ProjectiveLine T ↘ T)) :=
      hz ▸ inferInstance
    exact IsClosedImmersion.of_comp (projectiveZero T) (ProjectiveLine T ↘ T)
  obtain ⟨e⟩ := projectiveZero_dualIdeal T
  have hc := normalized_trace A T N hN hA hT hI (projectiveZeroCartier T)
    (projectiveSupported_chern A T N hN hA hT (projectiveZeroCartier T) e)
  have hi := congrArg (fun f ↦ f ≫ Etale.ordinaryFiniteProjectiveLineTrace N hN A hA T hT) hc
  calc
    _ = Etale.ordinaryFiniteP1ChernPushforward A N hA T
        (Etale.projectiveLineTraceDatum N hN A hA T hT).chern ≫
          Etale.ordinaryFiniteProjectiveLineTrace N hN A hA T hT := by
      simpa only [CoordinateLine.integration, Category.assoc] using hi
    _ = 𝟙 _ := Etale.projectiveLineTrace_chern N hN A hA T hT

/-- The scalar normalization remains identity after tensoring with any coefficient complex.

Source: current blueprint `det-sp-trace-basic`, Proof (2), coefficient-twisting step
(blueprint: lem-sp-affine-origin-line-normalization).

Proof: the ordinary tensor-trace equation expresses the twisted trace as conjugation
of the scalar trace by the coefficient right unitor. Substitute the preceding scalar
identity; functoriality of tensor and the inverse-unitor equation give identity.
-/
theorem affineOriginLine_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (M : Etale.DerivedCategoryModule A T) (hpf : IsIso (closedProjection A T M)) :
    (sectionComposition A T).inv.app M ≫
      (compact A T).map (tensorSupported A T N hN hA hT hI M hpf) ≫
      (CoordinateLine.adjunction A N hA T hN hT).counit.app M = 𝟙 _ := by
  exact normalized_tensor_trace A T N hN hA hT hI
    (affineOriginLine_scalar A T N hN hA hT hI) M hpf

/-- The zero section of the affine line is Cartier over every base.
Source: coordinate regularity in `det-sp-trace-basic`, Proof (2)
(blueprint: lem-sp-affine-origin-line-normalization).
Proof: it is a finite flat section of a smooth relative curve. The relative Cartier
criterion applied to the kernel closed subscheme gives an invertible ideal. -/
theorem affineOriginLine_cartier (T : Scheme.{u}) : (sectionMap T).ker.IsInvertible := by
  let p := AffineSpace PUnit.{u + 1} T ↘ T
  have : SmoothOfRelativeDimension 1 p := by
    simpa only [Nat.card_unique] using
      AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} T
  let z := sectionMap T
  let l := IsClosedImmersion.lift z z.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι z.ker).ge
  have : IsIso l := IsClosedImmersion.isIso_lift z z.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι z.ker).symm
  have hl : z.ker.subschemeι ≫ p = l := by
    rw [← IsClosedImmersion.lift_fac z z.ker.subschemeι
      (Scheme.IdealSheafData.ker_subschemeι z.ker).ge, Category.assoc,
      AffineSpace.zeroSection_comp_over, Category.comp_id]
  have : IsIso (z.ker.subschemeι ≫ p) := hl ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    inferInstance inferInstance inferInstance

/-- Proper projection at the coordinate section is invertible for all coefficients.
Source: proper projection formula in `det-sp-trace-basic`, Proof (2)
(blueprint: lem-sp-affine-origin-line-normalization).
Proof: the closed section is proper; apply the finite-coefficient projection formula
and then the canonical section pullback and coefficient unitor. -/
theorem affineOriginLine_projection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T] (M : Etale.DerivedCategoryModule A T) :
    IsIso (closedProjection A T M) := by
  exact closedProjection_isIso A T M

/-- The actual tensor Cartier arrow in the untransported coordinate right adjoint.
Source: `det-sp-trace-basic`, Proof (2), coefficient-twisting step
(blueprint: lem-sp-affine-origin-line-normalization). -/
def affineOriginLine_class
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (M : Etale.DerivedCategoryModule A T) :
    (closedImage A T).obj M ⟶ (Etale.affineTraceLineRight A N hA T).obj M :=
  tensorSupported A T N hN hA hT (affineOriginLine_cartier T) M
      (affineOriginLine_projection_isIso A T M) ≫
    (CoordinateLine.rightComparison A N hA T).inv.app M

/-- Push forward the tensor Cartier arrow with the identity-normalized section source.
Source: `det-sp-trace-basic`, Proof (2), coefficient-twisting step
(blueprint: lem-sp-affine-origin-line-normalization). -/
def affineOriginLine_section
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (M : Etale.DerivedCategoryModule A T) :
    M ⟶ (Etale.affineTraceLineLeft A T).obj
      ((Etale.affineTraceLineRight A N hA T).obj M) :=
  (sectionComposition A T).inv.app M ≫
    (Etale.affineTraceLineLeft A T).map (affineOriginLine_class A T N hN hA hT M)

/-- The tensor Cartier section is normalized for any normalized projective-line datum.
Source: `det-sp-trace-basic`, Proof (2), tensor trace and uniqueness of normalized data
(blueprint: lem-sp-affine-origin-line-normalization).
Proof: uniqueness of normalized Tate transport and projective data identifies the given
line adjunction with the canonical one. Expand transport of the right adjoint in the
proved tensor identity; functoriality gives exactly the displayed supported section. -/
theorem affineOriginLine_section_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤)))
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : Etale.OrdinaryFiniteP1Datum A N hA t T hT)
    (M : Etale.DerivedCategoryModule A T) :
    affineOriginLine_section A T N hN hA hT M ≫
      (Etale.affineTraceLineAdjunction A N hA t T hT D).counit.app M = 𝟙 _ := by
  have ht := Etale.ordinaryFiniteTwistTransport_unique A N hA t
    (Etale.projectiveLineTraceTransport N hN A hA)
  subst t
  have hD := Etale.ordinaryFiniteP1Datum_unique A N hA _ T hT D
    (Etale.projectiveLineTraceDatum N hN A hA T hT)
  subst D
  have h := affineOriginLine_tensor A T N hN hA hT (affineOriginLine_cartier T) M
    (affineOriginLine_projection_isIso A T M)
  simpa only [affineOriginLine_section, affineOriginLine_class, Functor.map_comp,
    Category.assoc, CoordinateLine.adjunction, Adjunction.ofNatIsoRight_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.id_obj, compact,
    Etale.rightDerivedLowerShriekOfCompactification, Etale.affineTraceLineLeft,
    Etale.affineTraceOpenLeft, Etale.ordinaryFinitePushforward,
    affineTraceLineCompactification, Functor.comp_map] using h

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
