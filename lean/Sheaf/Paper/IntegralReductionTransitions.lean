/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.NormalizedDVREffectivity

/-! # Canonical integral reduction adjunction and quotient transitions

Source: Weil conjectures blueprint, order 2132, coherent coefficient comparisons;
main-20261015, thm-pur-adic-reconstruction, normalized-system transitions.
(blueprint: def-pur-integral-reduction-transitions).

The two constructions of this node are the published declarations
`normalizedDVRIntegralAdjunction` (the tensor-unit-normalized derived adjunction
`L_n ⊣ Res_n`, the `.choose` of the published normalized adjunction) and
`normalizedDVRReductionTransition` (the inverse Hom-adjunction image under `𝔞_m` of
`η_n` followed by the inverse restriction comparison `e_{m,n}⁻¹`) of
`Sheaf.Paper.NormalizedDVREffectivity`, reexported here unchanged. They are not
redeclared, so that one definition per notion is kept.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

/-- The canonical semilinear reduction transition `t_{m,n}(M) : L_m M → Res_{m,n}(L_n M)`
of this node under its descriptive name: the transparent name of the published
`normalizedDVRReductionTransition`, the inverse Hom-adjunction image under the
normalized adjunction at `m` of the unit at `n` followed by the inverse canonical
restriction comparison. Lean index `n` denotes the exponent `n + 1`; equal indices
are included. Source: blueprint order 2132, last proof paragraph
(blueprint: def-pur-integral-reduction-transitions). -/
abbrev integralQuotientReductionTransition (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m)
    (M : completedIntegralDerivedCategory l E X D hl) :
    (scalarReductionDerivedExtension l E X m).obj M ⟶
      (normalizedDVRRes l E X h).obj
        ((scalarReductionDerivedExtension l E X n).obj M) :=
  normalizedDVRReductionTransition l E X D hl h M

end WeilConjectures
