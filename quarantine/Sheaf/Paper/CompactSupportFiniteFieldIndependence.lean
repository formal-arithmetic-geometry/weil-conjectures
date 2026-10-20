/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.SfScalarExtensionComposition

/-! # Independence of the finite coefficient field

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/
lem-weil-compact-support-finite-field-independence.md, node order 1495
(blueprint: lem-weil-compact-support-finite-field-independence).
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The compact-support values at any two finite coefficient stages are canonically
isomorphic via the specified beta-conjugated representative. A single normalized
finite action supplies all comparisons simultaneously. Identity and composition,
and independence under changing both the field and representative, are explicit. The
compactification is universally quantified because the source operation is defined
using an arbitrary compactification and the assertion is independent of that choice.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/
lem-weil-compact-support-finite-field-independence.md, node order 1495
(blueprint: lem-weil-compact-support-finite-field-independence).

Proof (the four paragraphs of the DAG node): finite-stage scalar extension and
compact-support compatibility give the comparison maps; representing the specified
common-stage isomorphism and its inverse over one larger finite field gives inverse
output maps; the common-stage equality criterion and scalar associators make the
result independent of auxiliary fields and representatives; identity and composition
follow by cancellation of the coefficient comparisons. -/
theorem sfCompactSupportFiniteFieldIndependence
    (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
    [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
    [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] :
    ∀ (c : Compactification f),
    ∃ S : SfCompactSupportCoefficientAction l K₀ _hl Ω c,
      (∀ (A P : Pair l Ω X) (α : A ≅ P),
        S.comparison α α = Iso.refl (S.value A)) ∧
      (∀ (A B C P : Pair l Ω X) (α : A ≅ P) (β : B ≅ P) (γ : C ≅ P),
        S.comparison α β ≪≫ S.comparison β γ = S.comparison α γ) ∧
      (∀ (A B : Pair l Ω X) (M N : Padic.FiniteCoefficientFields l Ω)
        (hAM : A.stage ≤ M) (hBM : B.stage ≤ M)
        (hAN : A.stage ≤ N) (hBN : B.stage ≤ N)
        (uM : StageHom A B ⟨M, hAM, hBM⟩)
        (uN : StageHom A B ⟨N, hAN, hBN⟩),
        ofHom A B M hAM hBM uM = ofHom A B N hAN hBN uN →
          S.representative A B M hAM hBM uM = S.representative A B N hAN hBN uN) ∧
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (_hEL : E ≤ L)
        (K_E : Stage l Ω X E) (K_L : Stage l Ω X L) (Kq : Pair l Ω X)
        (α_E : (⟨E, K_E⟩ : Pair l Ω X) ≅ Kq)
        (α_L : (⟨L, K_L⟩ : Pair l Ω X) ≅ Kq),
        ∀ (M : Padic.FiniteCoefficientFields l Ω) (hE : E ≤ M) (hL : L ≤ M)
          (uM : StageHom (⟨E, K_E⟩ : Pair l Ω X) (⟨L, K_L⟩ : Pair l Ω X)
            ⟨M, hE, hL⟩),
          ofHom (⟨E, K_E⟩ : Pair l Ω X) (⟨L, K_L⟩ : Pair l Ω X) M hE hL uM =
            α_E.hom ≫ α_L.inv →
          (S.comparison α_E α_L).hom =
            S.representative (⟨E, K_E⟩ : Pair l Ω X) (⟨L, K_L⟩ : Pair l Ω X)
              M hE hL uM) := by
  sorry

end WeilConjectures
