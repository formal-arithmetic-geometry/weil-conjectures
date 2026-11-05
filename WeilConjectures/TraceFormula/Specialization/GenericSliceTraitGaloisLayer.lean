/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.SliceTraitGaloisLayer

/-!

# The slice over a generic slice trait in Galois-layer form

Let `D` be a generic slice trait of `𝔸¹_S`, `S = Spec k'⟦t⟧` with `k'` separably closed
(`AlgebraicGeometry.GenericSliceTrait`), and `σ = NearbyCyclesModel.genericSliceTraitHom D n i`
the morphism of models from `𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S'` over `S'` to `𝔸ⁿ⁺¹_S` over `S`. As `D` is a slice
trait over `S` (`AlgebraicGeometry.GenericSliceTrait.toSliceTrait`), the change of geometric
generic fibres `σ.toCartesian` is, up to universal homeomorphisms, the projection of the Galois
layer of the pro-`p` extension `L^sep / L`, `L = Ω·Frac R ⊆ Ω'`
(`NearbyCyclesModel.Hom.traitChangeModel`). Hence its pullback exchange is a split monomorphism
with finite coefficients in which `p` is invertible
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom_of_finite`):
this is (M2) with torsion coefficients (SGA 4½, [Th. finitude], Lemme 3.4).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] [IsSepClosed k'] (D : GenericSliceTrait k') (n : ℕ)
  (i : Fin (n + 1))

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
