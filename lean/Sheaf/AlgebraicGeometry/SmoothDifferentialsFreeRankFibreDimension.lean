/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Differentials of a smooth morphism and fibre dimension

Source: Stacks Project, Morphisms, Lemma 02G1 (label lemma-smooth-omega-finite-locally-free).
(blueprint: lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- Stacks Project, Morphisms, Lemma 02G1.
(blueprint: lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension)
For a smooth morphism and a point, the relative Kähler differentials are free near
that point, with rank the dimension of the fibre at the corresponding point.

Proof:
1. By `lem-weil-pbc-smooth-locally-standard-smooth`, choose affine neighbourhoods
   on which the induced ring map has a standard smooth presentation in `n` variables
   with `c` equations and an invertible Jacobian minor.
2. By `lem-weil-pbc-standard-smooth-kahler-basis`, the differentials have the basis
   given by the last `n - c` coordinate differentials.
3. Identify the fibre near its point with the spectrum of the affine fibre ring,
   using `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`,
   `lem-weil-pbc-spec-residue-field-identification`,
   `lem-weil-pbc-open-fibre-product`, and `lem-weil-pbc-fibre-product-affine-spectra`.
   The local dimension is unchanged by this open restriction and homeomorphism,
   by `lem-weil-pbc-dimension-at-point-open-subspace`.
4. Base change preserves the standard smooth presentation by
   `lem-weil-pbc-standard-smooth-base-change`. The field case
   `lem-weil-pbc-standard-smooth-over-field-dimension-at-points` gives dimension
   `n - c`. This is nonnegative and equals the basis cardinality from step 2. -/
theorem smooth_differentials_free_rank_fibre_dimension
    (X S : Scheme.{u}) (f : X ⟶ S) [Smooth f] (x : X) :
    ∃ (d : ℕ),
        topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞) ∧
          ∃ (V : S.Opens) (W : X.Opens) (hWV : W ≤ f ⁻¹ᵁ V),
            x ∈ W ∧ IsAffineOpen V ∧ IsAffineOpen W ∧
              Nonempty (Module.Basis (Fin d) (Γ(X, W))
                (CommRingCat.KaehlerDifferential (f.appLE V W hWV))) := by
  obtain ⟨V, hV, W, hW, hx, hWV, hsm⟩ := Smooth.exists_isStandardSmooth f x
  let := (f.appLE V W hWV).hom.toAlgebra
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hsm.out
  have : Finite ι := hι
  have : Finite σ := hσ
  let d := P.dimension
  have hstd : (f.appLE V W hWV).hom.IsStandardSmoothOfRelativeDimension d :=
    P.isStandardSmoothOfRelativeDimension rfl
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  have hrel : SmoothOfRelativeDimension d (f.resLE V W hWV) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)]
    have : (RingHom.toMorphismProperty
        (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d))).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp <|
        (HasRingHomProperty.isLocal_ringHomProperty
          (@SmoothOfRelativeDimension d)).respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
        (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)))
        (arrowResLEAppIso f V W hWV)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hstd)
  have : SmoothOfRelativeDimension d (W.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f hWV]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE V W hWV ≫ V.ι) := inferInstance
    simpa using this
  let O := (f.fiberι (f x)) ⁻¹ᵁ W
  have hxO : f.asFiber x ∈ O := by
    change f.fiberι _ (f.asFiber x) ∈ W
    simpa using hx
  have hpb : IsPullback (f.fiberι (f x) ∣_ W)
      (O.ι ≫ f.fiberToSpecResidueField (f x))
      (W.ι ≫ f) (S.fromSpecResidueField (f x)) :=
    (isPullback_morphismRestrict (f.fiberι (f x)) W).paste_vert
      (IsPullback.of_hasPullback _ _)
  have : SmoothOfRelativeDimension d (O.ι ≫ f.fiberToSpecResidueField (f x)) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback hpb inferInstance
  have hdim := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension
    (O.ι ≫ f.fiberToSpecResidueField (f x)) d (⟨f.asFiber x, hxO⟩ : O)
  rw [IsOpen.topologicalKrullDimAt_eq O.isOpen hxO] at hdim
  refine ⟨d, hdim, V, W, hWV, hx, hV, hW, ?_⟩
  have : Algebra.IsStandardSmoothOfRelativeDimension d Γ(S, V) Γ(X, W) :=
    P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨eΩ⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.nonempty_linearEquiv_kaehlerDifferential
      (R := Γ(S, V)) (S := Γ(X, W)) d
  exact ⟨(Pi.basisFun (Γ(X, W)) (Fin d)).map eΩ.symm⟩

end AlgebraicGeometry
