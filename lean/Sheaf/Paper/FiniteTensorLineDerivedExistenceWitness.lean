/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.Paper.FiniteTensorReductionData

/-! # Existence of the prescribed derived signed-line comparison

Source: finite reduction of purity, proof Step 2; Stacks Tags 07A4 and 03EM.
(blueprint: lem-pur-finite-tensor-line-derived-existence-witness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/--
For a normalized ordinary signed-line map, the prescribed transpose is realized by
some derived comparison. The source-line local-freeness and scalar-extension
calculation construct this comparison on a cover trivializing the line; the
local maps agree on overlaps by the balancing and tensor equations, and exact
restriction transports the result to fixed-scalar coordinates. Localization of
the degree-zero single-complex calculation yields the displayed `HEq` equation.
This is the existence part of the unique comparison statement; uniqueness is
proved separately from injectivity of the scalar adjunction hom equivalence.
(blueprint: lem-pur-finite-tensor-line-derived-existence-witness)
-/
theorem exists_finiteTensorLineDerivedComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c) (r : ℤ) :
    ∃ b : (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
        (P.finiteReductionSetting m hm).finiteTensorFixedLine T r,
      (P.finiteTensorLineComparisonData m hm hmn T).Pointwise c r b := by
  sorry

end WeilConjectures.PurityFiniteSetting
