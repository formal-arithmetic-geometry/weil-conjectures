/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefVerdierWeilData
import WeilConjectures.SixFunctors.CoefWeilNormalizedDuality
import WeilConjectures.SixFunctors.CoefWeilExceptionalCompatibility

/-! # Weil equivariance of completed coefficient duality

Source: blueprint `cor-coef-verdier-weil-equivariance`, proof paragraphs 1--3
(blueprint: cor-coef-verdier-weil-equivariance).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures


/-- Completed-coefficient Verdier duality and exceptional adjunctions preserve Weil
pairs, with equivariant evaluation, biduality, scalar comparisons and compatibility
maps, without any Frobenius-stable integral lattice.
Source: literature/blueprint/latest, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance, statement and proof paragraphs 1--3
(blueprint: cor-coef-verdier-weil-equivariance).

Proof: lem-coef-weil-normalized-duality supplies BX on the actual geometric fiber,
its internal-Hom and dualizing identifications, and a normalized Weil structure WX.
For a descended f₀ use lem-coef-weil-left-exchange-compatibility to choose BY with
its normalized Weil structure WY and its exceptional system A, together with the
normalized left exchanges and the relative exceptional formula.
Finally lem-coef-weil-exceptional-compatibility constructs all required relative
Weil adjunctions from the canonical left exchanges and their coefficient squares.
That lemma uses a complete counit-transpose calculation for the right scalar square;
the actual units, counits and all underlying functors are retained. -/
theorem coef_verdier_weil_equivariance
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    CoefVerdierWeil.Conclusion D l hl Ω X₀ := by
  obtain ⟨BX, hIX, hωX, WX, hWX⟩ := coef_weil_normalized_duality D l hl Ω X₀
  refine ⟨BX, hIX, hωX, WX, hWX, ?_⟩
  intro Y₀ _ _ _ f₀ _ _ _ c₀
  obtain ⟨BY, A, hIY, hωY, hA, ⟨WY, hWY⟩, hL⟩ :=
    CoefVerdierWeil.coef_weil_left_exchange_compatibility D l hl Ω X₀ f₀ c₀ BX hIX hωX
  obtain ⟨L⟩ := hL WX WY
  exact ⟨BY, A, hIY, hωY, hA, WY, hWY,
    coef_weil_exceptional_compatibility D l hl Ω X₀ f₀ c₀ A WX WY L⟩

end WeilConjectures
