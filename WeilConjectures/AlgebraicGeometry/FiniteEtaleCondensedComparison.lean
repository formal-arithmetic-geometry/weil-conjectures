/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-! # Finite projection formula: etale-to-condensed comparison

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-pf-adic/det-thm-sf-pf-finite.proof.md`, general-k etale-to-condensed
realization of the compactification projection map (blueprint:
new-lem-det-sf-pf-finite-etale-condensed-comparison).

The statement uses the canonical compact-support comparison, the etale and pro-etale
compactification projection components, the canonical tensor comparison, and the
pullback target transport.  These are the constructions in
`AlgebraicGeometry.ProEtale.ProjectionComparisonEquation`; no arbitrary comparison
morphisms are introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- General-characteristic finite-level etale-to-condensed projection comparison.

Let `k` be a field of characteristic `p > 0`, let `l ≠ p` be prime, let `E / ℚ_l`
be finite with uniformizer data as in `coefficientExtensionRing`, and let
`A = O_E / varpi_E^n` with `n ≥ 1`.  Let `X,Y` be finite-type `k`-schemes and
`f : X ⟶ Y` a separated finite-type morphism with compactification `c`.  For
bounded constructible `M,H` with `H` of finite Tor amplitude, the canonical
comparison square commutes after the bounded-below witnesses are chosen.  The
conclusion is the typed equation in `ProjectionComparisonEquation`: its left
side is the pro-etale projection, the canonical pullback/tensor target transport,
and the compact-support comparison `C_(M ⊗ f^*H)`; its right side is
`V_Y(PF^(et,c))`, preceded by the inverse tensor comparison and `C_M ⊗ 1`.
No projection map is inverted.

Proof steps from the source: (1) Tor amplitude and exact extension by zero give
bounded-below inputs; (2) apply compact-support comparison to both inputs; (3)
apply the proper etale/pro-etale projection square; (4) apply open tensor
coherence and pullback compatibility; (5) identify the module-object projection
and open inverse with the pro-etale projection; (6) paste proper and open
squares; (7) use naturality, including the identity-open, identity-proper, and
zero-object cases.  Source: blueprint
`det-thm-sf-pf-finite.proof.md` (blueprint: new-lem-det-sf-pf-finite-etale-condensed-comparison). -/
theorem finite_etale_condensed_projection_comparison
    {k : Type u} [Field k] {p l : ℕ} [Fact p.Prime] [Fact l.Prime]
    [CharP k p] (_hl : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (H : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) X M)
    (_hH : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) Y H)
    (_hTor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing l E n) Y a b H) :
    ∃ (hM : _root_.DerivedCategory.TStructure.t.plus M)
      (hD : _root_.DerivedCategory.TStructure.t.plus
        (projectionComparisonTensor (Padic.coefficientExtensionRing l E n)
          (f := f) M H)),
      ProjectionComparisonEquation (Padic.coefficientExtensionRing l E n)
        c M H hM hD := by
  let A := Padic.coefficientExtensionRing l E n
  let hMb : _root_.DerivedCategory.TStructure.t.bounded M := by
    obtain ⟨r, s, _hrs, hbound⟩ := _hM.2
    exact ⟨⟨r, (_root_.DerivedCategory.isGE_iff M r).2
        (fun i hi ↦ hbound i (Or.inl hi))⟩,
      ⟨s, (_root_.DerivedCategory.isLE_iff M s).2
        (fun i hi ↦ hbound i (Or.inr hi))⟩⟩
  obtain ⟨a, b, ht⟩ := _hTor
  let hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor A (f := f) M H) := by
    exact Etale.plus_derivedTensor_leftDerivedUpperStar f hMb
      (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht)
  exact ⟨hMb.1, hD, projectionComparison_equation_of_plus A c M H hMb.1 hD⟩

end AlgebraicGeometry.ProEtale
