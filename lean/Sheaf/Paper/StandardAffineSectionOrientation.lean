/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E9
-/
module

public import Sheaf.Paper.CoordinateCounitArrows
public import Sheaf.Paper.SectionCoordinateChartMaps

/-! # Restriction of the normalized standard affine orientation at one

Source: sk-thm-dnc, Local construction, standard model, ordered trace base change.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open SectionComparisonArrows SectionLocalDualizingComparisons

/-- On the standard affine pair the two counit orientations have actual fibre value theta.
Written in their Tate coordinates this says theta is identity. No normalized deformation
comparison is assumed.
Source: sk-thm-dnc, standard model; orientation-charts Step 3
(blueprint: lem-trf-standard-affine-section-orientation).

Proof: Step 1 supplies the two counit-normalized affine adjunctions. Step 2 transposes
pullback of alpha followed by the exceptional mate: naturality of compact-support exchange
and the counit identity reduce it to pullback of the specified trace. Trace base change
identifies it with the new trace. Injectivity of adjunction gives the equality. Step 3
uses the base change i1 over X=A1_S and restricts to zero. In the Rees coordinates
x_j=t*u_j, at one x_j=u_j, giving theta i1*oF=oC. Cancelling oF gives the displayed
restriction of rawComparison. The inverse-image section compositor and canonical Tate
pullback are those of restrictionAtOne and affineSectionIso. The zero tower gives d=0.
-/
theorem sectionCoordinateCounit_standard (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ∃ (adjC : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣ affineRight A N hA S d)
      (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S) ↘ _) ⊣
          affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) S) d),
      CoordinateCounitArrows.IsNormalized N hN A hA t D S hS d adjC ∧
      @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D
        (AffineSpace (ULift.{u} (Fin 1)) S)
        (noetherianSource (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
        (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d adjF ∧
      (restrictionAtOne A S
        (rawComparison A N hN hA S hS d _ _
          (affineSectionIso A N hN hA S hS d
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) adjC)
          (@affineSectionIso A _ _ N hN hA (AffineSpace (ULift.{u} (Fin 1)) S)
            (noetherianSource (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
            (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) _) adjF))).hom =
        sectionMap A
          (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S) ↘ _)
          (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
          (AffineSpace.map (ULift.{u} (Fin d))
            (AffineSpace.oneSection (ULift.{u} (Fin 1)) S))
          (AffineSpace.isPullback_map _)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) _)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)
          (AffineSpace.zeroSection_comp_map _) := by
  sorry

/-- The normalized zero-section affine orientations commute with the standard one-fibre mate.
Source: sk-thm-dnc, Local construction, standard model; ordered trace base change
(blueprint: lem-trf-standard-affine-section-orientation).

Proof: normalization identifies the inverses of the affine dualizing comparisons with
standardAdjoint. The uniqueness of normalized projective-line data supplies base change
for the specified family D. The ordered affine trace counit base-change theorem and
naturality at the coefficient unit identify the pullback of towerAdjoint, through the
exceptional base-change mate, with towerAdjoint on the new base. This follows by applying
the adjunction homEquiv inverse to both sides: the defining mate equation and the trace
counit square give the same transpose. The canonical coordinate isomorphism from the
tower to affine space is Cartesian and natural in the base. Base-change transitivity
therefore transfers the equality to standardAdjoint. The root-normalized Tate products,
even-shift comparisons and pullback compositors identify the coefficient comparisons
with tatePullback. Invert the resulting square of affine dualizing isomorphisms and pull
it to the zero section. The zero-section base-change square and inverse-image section
compositor give precisely the displayed equation. This argument is valid for the empty
base, the zero ring and d=0: all tower counits at zero are identities; no positive-rank
or nonzero-coefficient cancellation is used.
-/
theorem standardAffineSectionOrientation_one (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (T : Scheme.{u}) [IsNoetherian T]
    [IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) T)]
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (adjC : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d)
    (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) T) ↘ _) ⊣
        affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) T) d)
    (hC : CoordinateCounitArrows.IsNormalized N hN A hA t D T hT d adjC)
    (hF : CoordinateCounitArrows.IsNormalized N hN A hA t D
      (AffineSpace (ULift.{u} (Fin 1)) T)
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT) d adjF) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.map
        (affineSectionIso A N hN hA (AffineSpace (ULift.{u} (Fin 1)) T)
          (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT) d
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) _) adjF).hom ≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.map
          (tatePullback A N hN hA (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT
            (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT) d).inv ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T)).hom.app
          (SectionLocalDualizingComparisons.tateObject A N hA T d) =
      SectionCoordinateChartMaps.standardFibreMap A T d ≫
        (affineSectionIso A N hN hA T hT d
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) T) adjC).hom := by
  obtain ⟨adjC', adjF', hC', hF', hstd⟩ :=
    sectionCoordinateCounit_standard N hN A hA t D T hT d
  have hci : affineDualizingIso A N hN hA T hT d adjC =
      affineDualizingIso A N hN hA T hT d adjC' := by
    apply Iso.ext_inv
    exact hC.trans hC'.symm
  have hfi : affineDualizingIso A N hN hA (AffineSpace (ULift.{u} (Fin 1)) T)
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT) d adjF =
      affineDualizingIso A N hN hA (AffineSpace (ULift.{u} (Fin 1)) T)
        (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT) d adjF' := by
    apply Iso.ext_inv
    exact hF.trans hF'.symm
  have hc : affineSectionIso A N hN hA T hT d
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) T) adjC =
      affineSectionIso A N hN hA T hT d
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) T) adjC' := by
    unfold affineSectionIso
    rw [hci]
  have hf : affineSectionIso A N hN hA (AffineSpace (ULift.{u} (Fin 1)) T)
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT) d
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) _) adjF =
      affineSectionIso A N hN hA (AffineSpace (ULift.{u} (Fin 1)) T)
        (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT) d
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) _) adjF' := by
    unfold affineSectionIso
    rw [hfi]
  rw [hc, hf]
  let oC := affineSectionIso A N hN hA T hT d
    (AffineSpace.zeroSection (ULift.{u} (Fin d)) T) adjC'
  have hn := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)
    (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T)).hom.naturality oC.inv
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hh := congrArg (fun z ↦ z ≫ oC.hom) hstd
  unfold restrictionAtOne rawComparison at hh
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] at hh
  rw [reassoc_of% hn] at hh
  simp only [Iso.inv_hom_id, Category.comp_id] at hh
  simpa only [SectionCoordinateChartMaps.standardFibreMap] using hh

end AlgebraicGeometry.Etale
