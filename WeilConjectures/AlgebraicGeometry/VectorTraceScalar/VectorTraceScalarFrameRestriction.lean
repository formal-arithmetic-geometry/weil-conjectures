/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarFrameRestrictionAffine
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarFrameRestrictionCompact

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The compact scalar comparison for one frame, before replacing the source trace by its
canonical glued integration map.  The proof is the proper/open scalar exchange and the
normalised Tate pullback calculation from the frame argument.
Source: blueprint/latest, sec-smooth-purity/sk-prop-an, paragraph 2.
(blueprint: new-lem-pur-vector-scalar-frame-restriction).
-/
theorem frame_scalar_restriction (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (ha : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤)))
      (d : ℕ), affine φ N hN hA hB T hT d ≫ affineTrace N hN B hB T hT d =
        (scalarExtension φ T).map (affineTrace N hN A hA T hT d) ≫ unit φ T)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (r : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank r]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S r F V)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT) :
    (ordinaryFinitePullback B V.ι).map
        (vector φ N hN hA hB S hS r F ≫ vectorBundleIntegration N hN B hB S hS r F) =
      (scalarPullbackIso φ V.ι).hom.app
          (vectorIntegrationSource A N hA S r F) ≫
        (scalarExtension φ V.toScheme).map
          (vectorIntegrationLocalTrace N hN A hA t D S hS r F V e) ≫
        (unit φ V.toScheme) ≫ (ordinaryFiniteUnitPullback B V.ι).inv := by
  letI := (vectorIntegration_geometry S r F).1
  letI := (vectorIntegration_geometry S r F).2.1
  letI := (vectorIntegration_geometry S r F).2.2
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  obtain ⟨tB, DB, _, _⟩ := exists_affineSpaceTopTrace N hN B hB
  have hnB : VectorIntegrationNormalization N hN B hB S hS r F
      (vectorBundleIntegration N hN B hB S hS r F) := by
    unfold vectorBundleIntegration vectorIntegrationGluing
    exact (existsUnique_vectorIntegrationGluing N hN B hB S hS r F).2.exists.choose_spec.2
  have hlocalB := hnB tB DB V e
  apply (cancel_mono (ordinaryFiniteUnitPullback B V.ι).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [hlocalB]
  unfold vector
  have hAffine := frame_scalar_restriction_affine N hN φ hA hB ha S hS r
  exact frame_scalar_restriction_compact N hN φ hA hB ha S hS r F V e hAffine t D tB DB


end AlgebraicGeometry.Etale.VectorTraceScalar
