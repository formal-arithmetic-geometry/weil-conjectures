/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData

/-! # The proper/open integral realization is a derived limit

Source: Bhatt--Scholze, Lemma 6.1.13, Definition 6.7.6 and Lemma 6.7.7;
Stacks Tags 0941 and 0F7J.
(blueprint: lem-pur-integral-proper-open-derived-limit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

/-- The ambient proper/open realization is a derived limit of its finite support tower.

Source: Bhatt--Scholze, Lemma 6.1.13, Definition 6.7.6 and Lemma 6.7.7;
Stacks Tags 0941 and 0F7J.
(blueprint: lem-pur-integral-proper-open-derived-limit).

Proof: present the complete constructible input by its strict quotient-reduction
system, retaining the canonical scalar-adjunction units and quotient transitions.
Quasi-compact open extension commutes with homotopy limits by Bhatt--Scholze
Lemma 6.1.13: the open/closed recollement triangle expresses it using product-
preserving functors. Its ringed slice presentation has the same property. Apply
this to the input reduction system. Exact open extension commutes with quotient
tensor; hence its value is the total inverse limit of the finite open extensions.
Apply the separately derived proper image.
Its right-adjoint comparison commutes with total inverse limits, including their
units. The resulting finite terms are the recorded finite compact-support terms:
identify constant-coefficient direct images sectionwise and identify the open
extensions by their unit-normalized adjunctions. These identifications respect the
quotient-induced transitions, because scalar restriction and proper/open comparison
maps preserve their adjunction units. The strict Roos model gives a distinguished
triangle with transition endomorphism one minus shift. Transport this triangle
along the term and transition identifications. Its vertex is the ambient proper/open
image, and the resulting triangle is precisely its asserted derived-limit property.
Only the existence of this triangle is asserted; no faithfulness of finite reduction
on arbitrary morphisms, and no uniqueness of triangle extensions, is used. -/
theorem integralProperOpen_isDerivedLimit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hunit : IsUnit (l : D.k))
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    letI : HasCountableProducts (DerivedCategory (scalarReductionSource l E Y)) :=
      integralOperationsDerivedCountableProducts l E Y
    IsDerivedLimit (fun n : ℕ ↦ sfCompactSupportTransition l E c M n)
      ((image (completed l E) c).obj M) := by
  sorry

end WeilConjectures
