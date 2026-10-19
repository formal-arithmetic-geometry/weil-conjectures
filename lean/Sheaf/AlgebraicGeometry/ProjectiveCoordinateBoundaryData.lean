/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The geometric construction underlying the projective coordinate-boundary lemma.

This packages the support computation, projectivity, Noetherian and compact base, and finite
geometric fibres.  Its proof is the coordinate-polynomial argument in the blueprint
(blueprint: new-lem-projective-coordinate-boundary-data): choose
nonzero polynomials cutting out the dense-open complements, invert their leading coefficients,
and use the resulting monic equations on every affine chart.  The finite spanning families give
finite geometric fibres, while the closed complement of a projective scheme is projective. -/
theorem exists_projective_coordinate_boundary_data
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of A)) [IsProjective f]
    (ι : Type v) [Finite ι] (U : ι → Y.affineOpens)
    (hcover : (⨆ i : ι, (U i).1) = ⊤)
    (m : ι → ℕ) (hm : ∀ i, 1 ≤ m i)
    (e : ∀ i, (U i).1.toScheme ⟶
      AffineSpace (ULift.{u} (Fin (m i))) (Spec (CommRingCat.of A)))
    [he : ∀ i, IsClosedImmersion (e i)]
    (hover : ∀ i, e i ≫ AffineSpace (ULift.{u} (Fin (m i)))
      (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A) = (U i).1.ι ≫ f)
    (V : ∀ i, Fin (m i) →
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of A))).Opens)
    (hV : ∀ i r, Dense (V i r : Set
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of A))))) :
    ∃ a : A, Nonempty (PrimeSpectrum.basicOpen a) ∧
      ∃ T : TopologicalSpace.Closeds ((pullback f (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a)) : Scheme.{u})),
        (T : Set ((pullback f (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a)) : Scheme.{u}))) =
          {x | ¬ ∃ (i : ι) (r : Fin (m i)) (y : (U i).1.toScheme),
            (U i).1.ι y = pullback.fst f
              (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
                (PrimeSpectrum.basicOpen a)) x ∧
            (e i ≫ AffineSpace.reindex
              (fun _ : ULift.{u} (Fin 1) ↦ (ULift.up r : ULift.{u} (Fin (m i))))
              (Spec (CommRingCat.of A))) y ∈ V i r} ∧
        IsProjective (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
          pullback.snd f (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
            (PrimeSpectrum.basicOpen a)))) ∧
        IsLocallyNoetherian ((Scheme.Opens.toScheme (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a))) ∧
        CompactSpace ((Scheme.Opens.toScheme (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a))) ∧
        ∀ t : (Scheme.Opens.toScheme (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a)),
          Finite ((pullback (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
            pullback.snd f (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
            (PrimeSpectrum.basicOpen a))))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (((Scheme.Opens.toScheme (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a))).residueField t)
              (AlgebraicClosure (((Scheme.Opens.toScheme (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a))).residueField t)))) ≫
            ((Scheme.Opens.toScheme (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a))).fromSpecResidueField t)) : Scheme.{u}) := by
  sorry

end AlgebraicGeometry
