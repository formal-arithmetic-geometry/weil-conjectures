/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.PureDimension
import Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.RingTheory.FiniteStability
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import Sheaf.AlgebraicGeometry.NodalPointEtaleLocality
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource

/-!
# Nodal families are étale local on the source

Source: Stacks Project, curves.tex, Tags 0C5C and 0C5D,
lemma-nodal-family-etale-local-source (blueprint: lem-trf-nodal-family-etale-source-locality).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A flat, locally finitely presented morphism with pure one-dimensional geometric
fibres and ordinary nodal completed local rings at every nonsmooth geometric fibre point.
Empty fibres are allowed: the pure-dimension condition has no components to test there.
Smoothness at a point means smoothness on an open neighbourhood of that point.
This is the inline notion in the source-locality statement, without connectedness,
properness, quasi-compactness, separatedness or Noetherian hypotheses.
Source: Stacks Project, curves.tex, Tags 0C59, 0C5A, 0C5C and 0C5D
(blueprint: lem-trf-nodal-family-etale-source-locality). -/
def IsNodalRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Flat f ∧ LocallyOfFinitePresentation f ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S),
      Scheme.IsPureDimension (pullback (C := Scheme.{u}) f g) 1 ∧
        ∀ x : pullback (C := Scheme.{u}) f g,
          (¬ ∃ V : (pullback (C := Scheme.{u}) f g).Opens,
            x ∈ V ∧ Smooth (V.ι ≫ pullback.snd f g)) →
          Nonempty
            (AdicCompletion
                (IsLocalRing.maximalIdeal ((pullback f g).presheaf.stalk x))
                ((pullback f g).presheaf.stalk x) ≃+*
              (MvPowerSeries (Fin 2) Ω ⧸
                Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                  (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)}))

/-- A jointly surjective family of étale source maps detects nodal relative curves.
The index type may be empty; joint surjectivity then forces the source to be empty.
Source: Stacks Project, curves.tex, Tag 0C5D, lemma-nodal-family-etale-local-source,
and Tag 0C5C (blueprint: lem-trf-nodal-family-etale-source-locality).

Proof plan, following the node:
1. Étale maps are flat. Apply lem-trf-relative-flatness-source-cover to the structure
   sheaf, whose pullback is the structure sheaf, to descend and ascend flatness.
2. Apply lem-trf-lfp-fppf-source-locality to descend and ascend local finite presentation.
3. Base change the covering to each geometric fibre using
   lem-weil-pbc-etale-covering-base-change; pullback pasting identifies the fibre maps.
4. The fibres are locally finite type over the field by
   lem-weil-pbc-finite-presentation-base-change-composition, hence locally Noetherian
   by pqf-lem-locnoeth-lft.
5. By lem-sbc-flat-composite-fibre-dimension-at-point and
   lem-weil-pbc-etale-smooth-zero-dimensional-fibres, dimensions at corresponding
   fibre points agree.
6. Use lem-sbc-equidimensional-open-local-dimension and
   lem-sbc-constant-local-dimension-components, on whole fibres, to ascend and descend
   pure dimension one. Joint surjectivity supplies lifts in the descent direction.
7. If f is nodal, lem-trf-etale-source-smoothness takes nonsmooth fibre points to
   nonsmooth points. Apply lem-trf-nodal-point-etale-locality to ascend the nodal
   completion condition.
8. Conversely lift every nonsmooth point along the covering. The same smoothness
   equivalence and nodal-point locality descend its completed local ring condition.
9. Empty sources and empty fibres have no points or components to test, so these
   arguments include the empty-cover case.
-/
theorem isNodalRelativeCurve_iff_etale_source_cover
    {X S : Scheme.{u}} (f : X ⟶ S) (I : Type v) (U : I → Scheme.{u})
    (h : ∀ i : I, U i ⟶ X) (hetale : ∀ i : I, Etale (h i))
    (hcover : ∀ x : X, ∃ (i : I) (y : U i), h i y = x) :
    IsNodalRelativeCurve f ↔ ∀ i : I, IsNodalRelativeCurve (h i ≫ f) := by
  sorry

end AlgebraicGeometry
