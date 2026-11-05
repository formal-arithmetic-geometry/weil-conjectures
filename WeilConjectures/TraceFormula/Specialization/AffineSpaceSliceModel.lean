/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessCases
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# The morphism of models over a coordinate generic slice

For `S = Spec k'⟦t⟧`, `K = k'(x)^alg` (`AlgebraicGeometry.traitSliceField`) and a coordinate `i`,
this file packages the coordinate generic slice `hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S`
(`AlgebraicGeometry.affineSpaceSlice`) as a morphism of the geometric standard models
(`NearbyCyclesModel.affineSpaceSliceHom`), with its maps of total spaces, special fibres and
geometric generic fibres. It is the slice along which Deligne proves the finiteness of nearby
cycles by induction on the relative dimension (SGA 4½, [Th. finitude], proof of Thm. 3.2).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k']

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
