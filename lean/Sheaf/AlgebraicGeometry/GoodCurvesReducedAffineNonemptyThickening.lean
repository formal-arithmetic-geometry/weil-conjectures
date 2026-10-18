/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.FiniteRadicialGenericResidueExtension
import Sheaf.AlgebraicGeometry.GoodCurvesSpreadGenericCompletion
import Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep

/-!
# Good curve diagrams over an affine base

Source: Stacks Project, More on Morphisms, Tag 0GK7, proof through the shrinking
which makes every W_i → T_i surjective.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Construct the curve presentation and a thickening locus which meets every fibre
of each smooth curve. Density is not asserted here.

Source: Stacks Project, More on Morphisms, Tag 0GK7, proof through the sentence
"Shrinking S once more we can assume W_i → T_i is surjective for all i".
(blueprint: lem-weil-pbc-good-curves-reduced-affine-nonempty-thickening)

Proof: Apply the field curve completion theorem to the generic fibre over κ(η).
It supplies a finite purely inseparable extension K and an explicit finite generic
diagram of normalization components with smooth projective completions and all the
finite-presentation and qcqs properties needed for descent. Apply the finite radicial
generic residue-field realization theorem to K. Keep its reduced affine cover and
its generic point, with the residue-field isomorphism compatible with κ(η) → K.
Install the supplied structural instances and apply the theorem spreading this
prescribed generic completion diagram. Its output is exactly the required presentation. -/
theorem exists_good_curves_reduced_affine_nonempty_thickening
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (hdim : topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
        (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i)
        (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧
        (∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i) ∧
          ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1) ∧
        ∃ W : (pullback f (g ≫ U.ι)).Opens,
          (∀ (i : Fin n) (s : T i),
            ∃ y : (j i ≫ p i).fiber s,
              ((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) y ∈ W) ∧
          IsThickening (pullback.snd ν W.ι) := by
  let := f.fiberOverSpecResidueField η
  have : IsSeparated (f.fiber η ↘ Spec (.of (S.residueField η))) := by
    change IsSeparated (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  have : LocallyOfFiniteType (f.fiber η ↘ Spec (.of (S.residueField η))) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  have : QuasiCompact (f.fiber η ↘ Spec (.of (S.residueField η))) := by
    change QuasiCompact (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  obtain ⟨K, hK, aK, hfin, hpure, hcurves⟩ :=
    exists_field_curve_completion_insep (S.residueField η) (f.fiber η) hdim
  let := hK
  let := aK
  have := hfin
  have := hpure
  obtain ⟨U₀, hηU₀, V₀, g₀, hUa, hVa, hVr, hgfin, hgsurj, hginj,
    η₀, hq, hη₀, e, he⟩ := exists_finite_radicial_generic_residue_extension η hη K
  let := hUa
  let := hVa
  let := hVr
  let := hgfin
  let := hgsurj
  let := hginj
  exact exists_good_curves_spread_generic_completion f η hη K
    U₀ hηU₀ V₀ g₀ η₀ hq hη₀ e he hcurves

end AlgebraicGeometry
