/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.AlgebraicGeometry.RationalSmoothPairSystem
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
import WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.SmoothColimitRegular
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.FiniteTensorVanishingColimit
import Mathlib.FieldTheory.SeparablyGenerated
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.RingTheory.SmoothPushoutFilteredColimitStage
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.Algebra.Category.Ring.FinitePresentation
import WeilConjectures.RingTheory.RegularComposition
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-! # Rational smooth approximation of principal singularity pairs

Source: Temkin, Non-embedded Desingularization, proof of Proposition 3.3.5, printed p.25,
with the printed reversal of source and target corrected
(blueprint: lem-per-elkik-rational-smooth-models).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Rational smooth models exist for principal singularity pairs and their finite disjoint
unions. Every regular map between positive thick fibres factors smoothly at a finite source
stage, on an open containing the image, with the target stage fixed. The second assertion
applies to any systems satisfying the stated model conditions, and any prescribed source
lower bound. It asserts only a map of the thick fibres.

Source: Temkin Proposition 3.3.5, proof p.25
(blueprint: lem-per-elkik-rational-smooth-models).

Proof plan, following the eight DAG steps:
1. Choose a smooth-transition rational coefficient system for the characteristic-zero field
(lem-per-char-zero-smooth-coefficient-system). Finite type over a field implies finite
presentation. Descend a presentation and a representative of the distinguished generator
by lem-kun-fp-algebra-descent; tensor-element colimits identify the resulting ring colimit.
2. The transition ring maps are smooth by base change, hence flat. Finite-type rings are
Noetherian. Apply lem-per-smooth-colimit-regular to every tail; the affine flatness criterion,
the smooth-affine criterion and the geometrically regular field-extension lemma identify the
corresponding regular scheme projections.
3. The kernel of multiplication by the descended generator is finite over the Noetherian
model. Flat tensor exactness identifies its limit with the zero kernel upstairs. Kill its
finite generators at a later stage by lem-pc-finite-tensor-vanishing-colimit. Flatness then
preserves the non-zero-divisor property throughout the tail.
4. The complement of the generator is regular over a perfect field, hence smooth. Apply
lem-sbc-smooth-pushout-filtered-colimit-stage to descend that smoothness, compose with the
smooth rational coefficient structure and use smooth-over-field regularity. Restrict to
the tail where each complement is regular.
5. The quotient universal property identifies the colimit of the quotients by the m-th
powers with the quotient upstairs. Apply the affine-transition limit theorem to spectra.
The quotient transitions are smooth base changes; smooth-colimit regularity gives the
regular fibre projections. Ideals extend by construction.
6. For a fixed target stage descend the fibre map and the pair equations simultaneously:
if t is the target generator and s the image of a chosen source-stage generator, write
f(t)=su and s=f(t)v. Use E=C[S,U,V]/(t-SU,S-tV), finite presentation factorization and
filtered-colimit zero detection to descend these equations and identify S with the source
generator at a later stage. This gives ideal preservation without changing the target index.
7. The descended map composed with the source projection is regular, by regular composition.
It is locally of finite presentation since both stage rings are finite type over Q. Apply
lem-per-regular-precomposition-smooth-image and lift the resulting open of the closed fibre
to an ambient source open. Factor through this open by the open-immersion lifting theorem.
Restricting preserves the ideal equality; no ambient lift to the target model is constructed.
8. For finite unions take products of directed index sets and finite products of coordinate
rings. Idempotents and their finitely many equations descend by the same finite-presentation
and zero-detection statements. Smoothness and regularity are local on open-and-closed
components, so maps may mix components. Empty unions and empty fibres use the zero ring
and the empty open. A prescribed source lower bound is absorbed by directedness. -/
theorem exists_rational_smooth_pair_models :
    (∀ (X : Scheme.{u}) (I : X.IdealSheafData),
      IsFiniteCharZeroSingularityPair X I → Nonempty (RationalSmoothPairSystem X I)) ∧
    (∀ (X Y : Scheme.{u}) (I : X.IdealSheafData) (J : Y.IdealSheafData),
      IsFiniteCharZeroSingularityPair X I → IsFiniteCharZeroSingularityPair Y J →
      ∀ (SX : RationalSmoothPairSystem X I) (SY : RationalSmoothPairSystem Y J)
        (m : ℕ), 1 ≤ m → ∀ (a : SX.Index) (b₀ : SY.Index)
        (h : (J ^ m).subscheme ⟶ (I ^ m).subscheme),
        IsRegularSchemeMorphism h →
        (I.comap (I ^ m).subschemeι).comap h = J.comap (J ^ m).subschemeι →
        ∃ b : SY.Index, b₀ ≤ b ∧
          ∃ (U : (SY.diagram.obj (op b)).Opens)
            (p : (J ^ m).subscheme ⟶ (SY.fibreOpen m (op b) U).toScheme)
            (v : (SY.fibreOpen m (op b) U).toScheme ⟶ (SX.thickDiagram m).obj (op a)),
            (∀ y : (J ^ m).subscheme,
              ((SY.thickProjection m).app (op b) ≫
                (SY.thickInclusion m).app (op b)) y ∈ U) ∧
            p ≫ (SY.fibreOpen m (op b) U).ι = (SY.thickProjection m).app (op b) ∧
            p ≫ v = h ≫ (SX.thickProjection m).app (op a) ∧
            Smooth v ∧
            (SX.thickIdeal m (op a)).comap v =
              (SY.thickIdeal m (op b)).comap (SY.fibreOpen m (op b) U).ι ∧
            v ≫ (SX.thickInclusion m).app (op a) ≫ SX.rationalMap.app (op a) =
              (SY.fibreOpen m (op b) U).ι ≫ (SY.thickInclusion m).app (op b) ≫
                SY.rationalMap.app (op b)) := by
  sorry

end AlgebraicGeometry
