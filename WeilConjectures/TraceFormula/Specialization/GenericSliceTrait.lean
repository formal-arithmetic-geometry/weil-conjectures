/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSliceCartesian
public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSliceModel
public import WeilConjectures.TraceFormula.Specialization.TraitChangeInvariance
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelWeaklyEtale
public import WeilConjectures.TraceFormula.Specialization.SliceTrait

/-!

# The strict localization of `𝔸¹_S` at the generic point of its special fibre

Let `S = Spec k'⟦t⟧` and `K = k'(x)^alg` (`AlgebraicGeometry.traitSliceField`). Deligne's proof of
the finiteness of nearby cycles (SGA 4½, [Th. finitude], 3.3–3.4) slices along the strict
localization `S'` of `𝔸¹_S` at the geometric generic point `x` of its special fibre: a strictly
henselian trait, weakly étale over `𝔸¹_S`, through which the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`AlgebraicGeometry.traitSlice`) factors.

`AlgebraicGeometry.GenericSliceTrait k'` packages such a trait `S' = Spec R` with compatible
geometric generic point `Spec Ω'` and closed point `Spec κ`. For such data, the morphism of models
over the coordinate generic slice (`NearbyCyclesModel.affineSpaceSliceHom`) factors as
```
(𝔸ⁿ_{K⟦t⟧} over Spec K⟦t⟧) ──τ──→ (𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S' over S') ──σ──→ (𝔸ⁿ⁺¹_S over S)
```
(`NearbyCyclesModel.genericSliceTraitChangeHom`, `NearbyCyclesModel.genericSliceTraitHom`),
where `τ` is a change of strictly henselian trait and `σ` has weakly étale morphism of total
spaces.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace GenericSliceTrait

attribute [instance] commRing isDomain isDiscreteValuationRing isStrictlyHenselianLocalRing field_Ω
  isAlgClosed field_κ isSepClosed weaklyEtale isLocalHom_ι isLocalHom_φ

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

end GenericSliceTrait

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k') (n : ℕ) (i : Fin (n + 1))

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
