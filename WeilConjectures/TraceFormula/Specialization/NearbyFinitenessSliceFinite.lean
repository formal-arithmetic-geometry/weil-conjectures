/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitExists
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUnramified
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelWeaklyEtale
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeFiniteCoefficient

/-!

# The slice step of Deligne's induction with finite coefficients

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic exponent `p`, and `T` a finite
discrete ring in which `p` is invertible. For a complex `C` of `T̲`-modules on `𝔸ⁿ⁺¹_S` which is
bounded below of étale origin and a coordinate `i`, the pullback exchange
`α : Lhᵢ,ₛ^* Ψ C ⟶ Ψ_K (Lhᵢ^* C)` of the morphism of geometric models over the coordinate generic
slice (`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_finite`; SGA 4½,
[Th. finitude], Lemme 3.3). As for `ℚ̄_ℓ`-coefficients
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom`), the slice factors
through a generic slice trait `S'` (`AlgebraicGeometry.nonempty_genericSliceTrait`): the change of
trait `Spec K⟦t⟧ ⟶ S'` has invertible exchange by Th. finitude 3.7 with finite coefficients
(`ProEtale.CondensedRing.isIso_pullbackExchange_app_of_isPullback_trait_finite`), and the slice
over `S' ⟶ S` has split exchange: weakly étale base change, then the averaging (M2) with finite
coefficients
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom_of_finite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.GenericSliceTrait

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

end AlgebraicGeometry.GenericSliceTrait

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] [IsSepClosed k']
  (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
