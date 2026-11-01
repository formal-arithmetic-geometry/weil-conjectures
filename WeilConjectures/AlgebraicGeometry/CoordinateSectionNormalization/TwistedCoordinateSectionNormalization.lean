/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionCartier
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.TwistedCoordinateSectionSign

import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.CoordinateSectionProjectiveTrace
import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.CoordinateSectionTensorTrace
import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.CoordinateSectionSiteTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateCartierBoundarySign

/-!
# Twisted coordinate-section Kummer normalization

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, "In rank one this is the supported
coordinate orientation: the Cartier map ... integrates to 1", the even shifts and twists
sentence, and the finite etale-origin transport sentence; the latest blueprint version of
this proof states the boundary integral -1 used for the sign clause
(blueprint: lem-pur-twisted-coordinate-section-normalization).

The previously recorded coordinate arrows supply all maps. This module assembles their
normalizations at every annihilating exponent, without a ramification divisibility premise.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization

open AffineLinePurity

/-- The ordinary, closed-coprojection and pro-etale normalizations at every positive root
exponent killing the fixed coefficient ring. Invertibility on the base is a conclusion.
Source: blueprint cor-pur-affine-space-zero-section-purity.proof.md, rank-one calculation
and even-shift paragraph (blueprint: lem-pur-twisted-coordinate-section-normalization). -/
def NormalizationAt (T : Scheme.{u}) (P : WeilConjectures.PurityFiniteSetting.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (hI : (sectionMap T).ker.IsInvertible) : Prop :=
  ∀ (b : ℕ) (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0),
    ∃ hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤)),
      OrdinaryNormalization (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI ∧
      CoprojectionNormalization (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI ∧
      ProNormalization T P b hA aT hT hI

/-- The positive supported coordinate Cartier class integrates to one, including all Tate
inputs, under the actual integration-transposed comparison. Its boundary orientation has
opposite sign on the domain of the affine-line datum.

Source: blueprint cor-pur-affine-space-zero-section-purity.proof.md, rank-one supported
Cartier normalization, even shifts and twists, and finite-site transport
(blueprint: lem-pur-twisted-coordinate-section-normalization).

Proof: The affine-line zero section is a relative effective Cartier divisor: identify it
with the closed subscheme of its kernel and apply the finite-flat relative Cartier
criterion to the smooth line projection and its section equation
(lem-pc-cartier-criterion). Finite type over the field gives IsNoetherian T
(lem-weil-pbc-finite-type-over-noetherian). The projective zero section is closed because
its composite with the separated projective projection is the identity.
Apply lem-pur-coordinate-section-projective-trace: the dual ideal is O(1), and forgetting
support gives its positive Chern class. Compose the open-counit equation with the actual
projective trace. By the definition of CoordinateLine.integration and
projectiveLineTrace_chern (def-amb-p1-trace), both scalar integrals are the identity.
Apply lem-pur-coordinate-section-tensor-trace to obtain the canonical closed coprojection
formula and the tensor and exceptional transpose equations. These give OrdinaryNormalization.
Apply lem-pur-coordinate-section-site-transport to obtain CartierRealization, with one
supported-unit-normalized source comparison for every exponent, and ProNormalization.
The comparison uses the actual integration transpose of def-pur-affine-line-purity-comparison.
For every exponent, primeUnit.pow supplies hT after Nat.cast_pow. Assemble NormalizationAt.
Finally lem-pur-coordinate-cartier-boundary-sign gives CoordinateCartierSign: the signed
relative cone sends the localization boundary to the negative Cartier class. Package the
Cartier, Noetherian and closed-immersion witnesses, preserving the instance-quantified
normalization clauses. No flatness over Z/ell^a or divisibility of the level is used. -/
theorem twistedCoordinateSectionNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] :
    ∃ hI : (sectionMap T).ker.IsInvertible,
      IsNoetherian T ∧ CartierRealization T P aT hI ∧ P.CoordinateCartierSign T aT ∧
      IsClosedImmersion (projectiveZero T) ∧
      (∀ [IsNoetherian T] [IsClosedImmersion (projectiveZero T)], ProjectiveNormalization P T) ∧
      ∀ [IsNoetherian T], NormalizationAt T P aT hI := by
  let : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  have hsection : sectionMap T ≫ (AffineSpace PUnit.{u + 1} T ↘ T) = 𝟙 T :=
    AffineSpace.zeroSection_comp_over PUnit.{u + 1} T
  have hI : (sectionMap T).ker.IsInvertible := by
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
        (Scheme.IdealSheafData.ker_subschemeι z.ker).ge, Category.assoc, hsection,
        Category.comp_id]
    have : IsIso (z.ker.subschemeι ≫ p) := hl ▸ inferInstance
    exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
      inferInstance inferInstance inferInstance
  have hprojective : IsClosedImmersion (projectiveZero T) := by
    have heq : projectiveZero T ≫ (ProjectiveLine T ↘ T) = 𝟙 T := by
      rw [projectiveZero, Category.assoc, ProjectiveLine.affineChart_over, hsection]
    have : IsClosedImmersion (projectiveZero T ≫ (ProjectiveLine T ↘ T)) :=
      heq ▸ inferInstance
    exact IsClosedImmersion.of_comp (projectiveZero T) (ProjectiveLine T ↘ T)
  let := hprojective
  have hsite := coordinateSectionSiteTransport P T aT hI
  refine ⟨hI, inferInstance, hsite.1, P.coordinateCartierBoundarySign T aT,
    hprojective, ?_, ?_⟩
  · intro _ _
    exact (coordinateSectionProjectiveTrace P T).1
  · intro _ b hA
    let N := P.coefficients.l ^ (b + 1)
    have hN : 0 < N := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
    have hT : IsUnit (N : Γ(T, ⊤)) := by
      simpa only [N, Nat.cast_pow] using (primeUnit P T aT).pow (b + 1)
    have hchern := (coordinateSectionProjectiveTrace P T).2 b hA hT hI
    have hintegral :
        (sectionComposition (Ring P) T).inv.app (Etale.ordinaryFiniteUnit (Ring P) T) ≫
          (compact (Ring P) T).map (restrictedSupported (Ring P) T N hN hA hT hI) ≫
          CoordinateLine.integration (Ring P) N hA T hN hT =
        Etale.ordinaryFiniteP1ChernPushforward (Ring P) N hA T
          (Etale.projectiveLineTraceDatum N hN (Ring P) hA T hT).chern ≫
          Etale.projectiveLineTrace N hN (Ring P) hA T hT := by
      simpa only [CoordinateLine.integration, Category.assoc] using
        congrArg (fun f ↦ f ≫ Etale.projectiveLineTrace N hN (Ring P) hA T hT) hchern
    have hscalar :
        (sectionComposition (Ring P) T).inv.app (Etale.ordinaryFiniteUnit (Ring P) T) ≫
          (compact (Ring P) T).map (restrictedSupported (Ring P) T N hN hA hT hI) ≫
          CoordinateLine.integration (Ring P) N hA T hN hT = 𝟙 _ :=
      hintegral.trans (Etale.projectiveLineTrace_chern N hN (Ring P) hA T hT)
    obtain ⟨hcoprojection, htensor⟩ :=
      coordinateSectionTensorTrace (Ring P) T N hN hA hT hI hscalar
    have hord : OrdinaryNormalization (Ring P) T N hN hA hT hI :=
      ⟨hchern, hintegral, hscalar, htensor⟩
    exact ⟨hT, hord, hcoprojection, hsite.2 b hA hT hord hcoprojection⟩

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
