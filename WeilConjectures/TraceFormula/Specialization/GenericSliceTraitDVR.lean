/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSlicePoint
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.StrictHenselizationDimension
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import WeilConjectures.RingTheory.StrictHenselizationRegular

/-!

# The strict localization of `𝔸¹_S` at the generic point of its special fibre is a trait

Let `S = Spec k'⟦t⟧`, `K = k'(x)^alg` and `s = genericSlicePoint k' : Spec K ⟶ 𝔸¹_S` the
geometric point at the generic point of the special fibre `𝔸¹_{k'}`. The image of `s` in
`Spec k'⟦t⟧[x]` is the prime `(t)` (as `x` is transcendental over `k'`), so the local ring of
`𝔸¹_S` there is a noetherian local domain with principal maximal ideal `(t) ≠ 0`, i.e. a discrete
valuation ring. Being regular of dimension one passes to strict henselizations, so the strict
henselization `𝒪^{sh}_{𝔸¹_S, s}` is a discrete valuation ring as well.

## Main results

- `AlgebraicGeometry.ker_genericSlicePointRingHom`: the prime of `k'⟦t⟧[x]` under `s` is `(t)`.
- `AlgebraicGeometry.isDomain_strictHenselization_genericSlicePoint`
- `AlgebraicGeometry.isDiscreteValuationRing_strictHenselization_genericSlicePoint`
- `AlgebraicGeometry.maximalIdeal_strictHenselization_genericSlicePoint`: `t` is a uniformizer.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

open Scheme

variable (k' : Type u) [Field k']

end AlgebraicGeometry
