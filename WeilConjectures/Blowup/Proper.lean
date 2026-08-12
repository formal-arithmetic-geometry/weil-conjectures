/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Gluing

/-!

# Properness of the blow-up

We prove that the blow-up of a scheme along a finite-type quasi-coherent ideal is
proper over the base (blueprint: `thm:nagata-global-blowup-proper`; proof order
item 14).

The affine case reduces to Mathlib's properness of `Proj` over its degree-zero
spectrum: the Rees algebra of a finitely generated ideal is of finite type over its
degree-zero part (`AlgebraicGeometry.algebraFiniteType_reesGradingZero`, from
`reesAlgebra.fg`), whence `Proj.toSpecZero` of the Rees grading is proper. The global
case follows because properness is Zariski-local on the target and the blow-up
restricts to the affine blow-up over every affine open.

## Main results

- `AlgebraicGeometry.AffineBlowup.isProper_toSpec`: the affine blow-up of a finitely
  generated ideal is proper (blueprint: `lemma:nagata-affine-blowup-proper`);
- `AlgebraicGeometry.Scheme.IdealSheafData.isProper_blowupMap`: the blow-up of a
  finite-type quasi-coherent ideal is proper
  (blueprint: `thm:nagata-global-blowup-proper`). The finite-type hypothesis is
  phrased as finite generation of the ideal of sections on every affine open, which is
  `Scheme.IdealSheafData.FiniteType` of `WeilConjectures.Blowup.Exceptional`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Affine

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The Rees algebra of a finitely generated ideal is of finite type over the
degree-zero part of its grading. -/
lemma algebraFiniteType_reesGradingZero (hI : I.FG) :
    Algebra.FiniteType (reesGrading I 0) (reesAlgebra I) := by
  have h1 : Algebra.FiniteType A (reesAlgebra I) :=
    (Subalgebra.fg_iff_finiteType _).mp (reesAlgebra.fg hI)
  rw [← RingHom.finiteType_algebraMap] at h1 ⊢
  have hcomp : (algebraMap (reesGrading I 0) (reesAlgebra I)).comp
      (reesGradingZero I).toRingHom = algebraMap A (reesAlgebra I) := by
    ext a
    rfl
  rw [← hcomp] at h1
  exact RingHom.FiniteType.of_comp_finiteType h1

/-- **Properness of the affine blow-up**: the blow-up of `Spec A` along a finitely
generated ideal is proper over `Spec A`.
(Blueprint: `lemma:nagata-affine-blowup-proper`.) -/
theorem AffineBlowup.isProper_toSpec (hI : I.FG) : IsProper (AffineBlowup.toSpec I) := by
  haveI := algebraFiniteType_reesGradingZero I hI
  haveI : IsIso (Spec.map (CommRingCat.ofHom (reesGradingZero I).toRingHom)) := by
    rw [isIso_SpecMap_iff]
    exact (reesGradingZero I).bijective
  unfold AffineBlowup.toSpec
  rw [MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  infer_instance

end Affine

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Properness of the blow-up** (blueprint: `thm:nagata-global-blowup-proper`): the
blow-up of a scheme along a finite-type quasi-coherent ideal is proper over the
base. -/
theorem isProper_blowupMap (hI : ∀ U : X.affineOpens, (I.ideal U).FG) :
    IsProper I.blowupMap := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X) fun U ↦ ?_
  have e : Arrow.mk (I.blowupMap ∣_ U.1.ι.opensRange) ≅ Arrow.mk (I.blowupNatTrans.app U) :=
    morphismRestrictArrowIso I.blowupMap (I.blowupNatTrans.app U) (I.blowupι_blowupMap U)
      (by rw [Scheme.Opens.opensRange_ι]; exact I.blowupMap_preimage U)
  have hres : IsProper (I.blowupMap ∣_ U.1.ι.opensRange) := by
    rw [MorphismProperty.arrow_mk_iso_iff (P := @IsProper) e, I.blowupNatTrans_app U]
    haveI := AffineBlowup.isProper_toSpec (I.ideal U) (hI U)
    rw [MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
    infer_instance
  rwa [Scheme.Opens.opensRange_ι] at hres

end Scheme.IdealSheafData

end AlgebraicGeometry
