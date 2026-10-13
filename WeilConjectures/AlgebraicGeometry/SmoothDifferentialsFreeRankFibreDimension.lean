/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

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
  classical
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := (Smooth.iff_forall_exists_isStandardSmooth f).mp ‹_› x
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨pres⟩⟩ := hf.out
  have : Fintype ι := Fintype.ofFinite _
  have : Fintype σ := Fintype.ofFinite _
  refine ⟨pres.dimension, ?_, U, V, e, hx, hU, hV, ⟨?_⟩⟩
  · have : IsAffine U := hU
    have : IsAffine V := hV
    have hres : SmoothOfRelativeDimension pres.dimension (f.resLE U V e) := by
      rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension pres.dimension)]
      have : (RingHom.toMorphismProperty (RingHom.Locally
          (RingHom.IsStandardSmoothOfRelativeDimension pres.dimension))).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp <|
          (HasRingHomProperty.isLocal_ringHomProperty
            (@SmoothOfRelativeDimension pres.dimension)).respectsIso
      exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
          (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension pres.dimension)))
          (arrowResLEAppIso f U V e)).mpr
        (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
          (pres.isStandardSmoothOfRelativeDimension rfl))
    let W := (f.fiberι (f x)) ⁻¹ᵁ V
    have hW : f.asFiber x ∈ W := by
      change f.fiberι _ (f.asFiber x) ∈ V
      rwa [Scheme.Hom.fiberι_asFiber]
    have : SmoothOfRelativeDimension pres.dimension (V.ι ≫ f) := by
      rw [← Scheme.Hom.resLE_comp_ι f e]
      have : SmoothOfRelativeDimension (pres.dimension + 0) (f.resLE U V e ≫ U.ι) :=
        inferInstance
      simpa using this
    have hpb : IsPullback (f.fiberι (f x) ∣_ V) (W.ι ≫ f.fiberToSpecResidueField (f x))
        (V.ι ≫ f) (S.fromSpecResidueField (f x)) :=
      (isPullback_morphismRestrict (f.fiberι (f x)) V).paste_vert
        (IsPullback.of_hasPullback _ _)
    have : SmoothOfRelativeDimension pres.dimension
        (W.ι ≫ f.fiberToSpecResidueField (f x)) := by
      have := smoothOfRelativeDimension_isStableUnderBaseChange (n := pres.dimension)
      exact MorphismProperty.of_isPullback hpb inferInstance
    rw [← IsOpen.topologicalKrullDimAt_eq W.isOpen hW]
    exact @topologicalKrullDimAt_eq_of_smoothOfRelativeDimension _ _ _
      (W.ι ≫ f.fiberToSpecResidueField (f x)) pres.dimension this ⟨_, hW⟩
  · refine pres.basisKaehler.reindex (Fintype.equivFinOfCardEq ?_)
    simp only [Fintype.card_compl_set, Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
      Set.card_range_of_injective pres.map_inj]

end AlgebraicGeometry
