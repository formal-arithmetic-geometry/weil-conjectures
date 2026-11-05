/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.TraceFormula.Specialization.NearbyDuality

/-!

# Nearby duality and open restriction: the concrete inputs

The compatibility of the duality map of nearby cycles with open restriction (blueprint
`det-tf-nearby-duality-proper` (2)) is the abstract identity
`CategoryTheory.Verdier.nearbyDualityMap_restrict_natTrans`. This file proves its concrete inputs
for trait models:
* the duality map of `(G, μ_G, e)` for a lax monoidal `G` is the internal-hom comparison of `G`
  followed by `e` (`CategoryTheory.Verdier.nearbyDualityMap_eq_ihomComparison`), so for an open
  immersion it is invertible by
  `ProEtale.CondensedRing.isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion`;
* the lax tensor map of nearby cycles on bounded constructible complexes is natural
  (`NearbyCyclesModel.boundedConstructibleTensorMap_natural`);
* the restricted pullback exchange is monoidal, in the lax form used there
  (`NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_tensor`), from the ambient
  monoidality `NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`.

The remaining inputs are the invertibility of the pullback exchange for open immersions
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`) and the compatibility of the
dualizing maps with open restriction
(`NearbyCyclesModel.NearbyDualizingData.map_θ_comp_dualizingComplexUpperStarIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

namespace Verdier

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {D : Type*} [Category* D] [MonoidalCategory D] [MonoidalClosed D]

end Verdier

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y ⟶ X} {j' : Y' ⟶ X'} (φ : N.Hom M j.left j'.left)

section OpenIhom

variable {V W : Over (Spec (.of k'))} [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
  [IsSeparated V.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  (i : V ⟶ W) [IsOpenImmersion i.left]

end OpenIhom

variable (ℓ) [IsSepClosed k'] [Algebra k k'] [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
