/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions
import Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism
import Sheaf.FieldTheory.SeparablyGeneratedSeparable
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Normalization after arbitrary extension of the ground field

Source: Stacks Project, Varieties, Tag 0C3N, lemma-normalization-and-change-of-fields
(blueprint: lem-per-normalization-field-extension-homeomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical comparison from the componentwise normalization after field extension
is a universal homeomorphism. Its two projection equations characterize it uniquely over
`X_K`, so no choice of a comparison morphism is part of the hypotheses.
Source: Stacks Project, Varieties, Tag 0C3N, lemma-normalization-and-change-of-fields
(blueprint: lem-per-normalization-field-extension-homeomorphism).

Proof:
1. On a nonempty affine chart Spec A of X, let A' be its integral closure in Frac A.
For every extension L/k put B_L = A tensor L, R_L = (B_L)_red, and Q_L = Q(R_L).
Finite type over L makes R_L Noetherian (`lem-weil-pbc-finite-type-over-noetherian`).
The affine-chart theorem `lem-per-componentwise-normalization-affine-charts` and
`lem-weil-pbc-reduced-noetherian-total-ring-fractions` identify the normalization chart
with Spec B'_L, where B'_L is the integral closure of B_L in Q_L. Integrality in the
finite product of component fields is coordinatewise: multiply the monic polynomials.
2. By `lem-per-reduced-total-fractions-field-extension`, Frac A maps to Q_K and takes
A' into B'_K, giving A' tensor K -> B'_K, a' tensor c maps to a'c. Localization
compatibility (`lem-weil-pbc-integral-closure-commutes-localization`) glues these maps
into b with the displayed projections. Each denominator from A remains a nonzerodivisor
on each reduced component after field extension. Thus any map with these projections
must send a fraction a/s to its prescribed fraction, proving uniqueness on each chart
and globally. This is the canonical normalization comparison of Stacks 0C3N.
3. Flatness over k (`lem-weil-pbc-module-over-field-flat`) embeds A' tensor K into
Frac A tensor K. The kernel of the latter's map to Q_K is nil by the fraction-ring
lemma. Consequently the kernel of A' tensor K -> B'_K is nil, even if its source is
nonreduced.
4. For separable K/k, `lem-weil-pbc-reduced-algebraic-normalization-field-change`
identifies this comparison with an isomorphism. Otherwise k has prime characteristic
p > 0: in characteristic zero, every finitely generated subextension has a separating
transcendence basis (`lem-weil-pbc-perfect-field-separating-basis`), and is separable
by `lem-weil-pbc-separably-generated-separable`, hence K/k is separable by definition.
5. For b in B'_K, choose a fraction c/d and a monic integral equation. The finitely
many scalar coefficients in c, d and that equation generate a field H/k inside K.
The fraction-ring lemma reflects the nonzerodivisor condition for d and the equation,
so b descends to an integral element b_H in Q_H.
6. Choose a finite transcendence basis of H/k
(`lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`). Let E be the
separable closure of k(t) in H. By `lem-weil-pbc-separable-first-purely-inseparable`,
H/E is purely inseparable, while E/k is separably generated and hence separable.
Choose a common q = p^n, n > 0, taking the finitely many coefficients into E.
Frobenius takes c^q, d^q and all coefficients of the equation into the rings over E.
7. Injectivity Q_E -> Q_H reflects both the nonzerodivisor condition and the equation
raised to q, so b_H^q descends to an integral element in B'_E. The separable comparison
gives its preimage in A' tensor E, hence b^q lies in the image of A' tensor K -> B'_K.
Tower compatibility of the fraction-ring maps identifies these images.
8. Apply `lem-pur-power-generated-spectrum-homeomorphism`: the kernel is nil, each
target element has a positive p-power in the image, and p^n times that element is zero.
Thus each affine restriction of b is a universal homeomorphism. After any base change,
the affine opens still cover and the inverse homeomorphisms agree on overlaps, hence
glue to the required global inverse. -/
theorem normalization_field_extension_homeomorphism
    {k : Type u} [Field k] (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType q] [QuasiCompact q]
    (K : Type u) [Field K] [Algebra k K] :
    ∃! b : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reducedNormalization ⟶
        pullback (X.fromNormalization ≫ q)
          (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      (b ≫ pullback.fst _ _ ≫ X.fromNormalization =
        (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
          pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      (b ≫ pullback.snd _ _ =
        (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
          pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      (topologically IsHomeomorph).universally b := by
  sorry

end AlgebraicGeometry
