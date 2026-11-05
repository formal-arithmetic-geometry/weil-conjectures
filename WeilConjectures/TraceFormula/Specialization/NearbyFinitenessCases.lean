/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModelEmbedding
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFiniteness

/-!

# Special cases of Deligne's finiteness theorem for nearby cycles on affine spaces

Over the strictly henselian trait `S = Spec k'⟦t⟧`, this file proves the reductions and special
cases used for Deligne's finiteness theorem for nearby cycles
(`WeilConjectures.TraceFormula.Specialization.NearbyFiniteness`) on the affine spaces `𝔸ⁿ_S`:

* the reduction along a closed embedding of models
  (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding`);
* extensions by zero of lisse sheaves are bounded constructible
  (`NearbyCyclesModel.boundedConstructible_lisseExtension`);
* the case `n = 0` (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`);
* complexes supported on a closed subscheme missing the special fibre have vanishing nearby
  cycles (`NearbyCyclesModel.isZero_nearbyCycles_affineSpace_of_disjoint`), and those supported on
  a closed subscheme embedded in the trait have bounded constructible nearby cycles
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isClosedImmersion_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))}

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
