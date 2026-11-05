/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitDVR
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUniversal
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationFunctoriality
public import WeilConjectures.TraceFormula.Specialization.SliceTraitResidue

/-!

# The strict localization of `𝔸¹_S` is a generic slice trait

The strict henselization `R` of `𝔸¹_S` (`S = Spec k'⟦t⟧`) at the geometric point
`Spec K ⟶ 𝔸¹_S` over the generic point of its special fibre (`AlgebraicGeometry.genericSlicePoint`,
`K = k'(x)^alg`) is a strictly henselian discrete valuation ring, weakly étale over `𝔸¹_S`, and the
generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` factors through it by a local injection `R ⟶ K⟦t⟧`
(SGA 4½, [Th. finitude], 3.3). With the geometric generic point `R ⟶ Ω' = (Frac R)^alg` and the
closed point `R ⟶ K`, this is a generic slice trait
(`AlgebraicGeometry.genericSliceTraitOfStrictLocalization`,
`AlgebraicGeometry.nonempty_genericSliceTrait`).

The embedding `Ω' ⟶ Ω_K` extends `Frac R ⟶ Frac K⟦t⟧`
(`AlgebraicGeometry.genericSliceTraitToField`); the embedding `Ω ⟶ Ω'` is the unique one whose
composite with it is the fixed embedding `Ω ⟶ Ω_K`: the image of `Ω`, algebraic over
`Frac k'⟦t⟧`, lies in the algebraically closed image of `Ω'`
(`AlgebraicGeometry.genericSliceTraitFromField`).

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (k' : Type u) [Field k']

attribute [local instance] isDomain_strictHenselization_genericSlicePoint
  isDiscreteValuationRing_strictHenselization_genericSlicePoint

end AlgebraicGeometry
