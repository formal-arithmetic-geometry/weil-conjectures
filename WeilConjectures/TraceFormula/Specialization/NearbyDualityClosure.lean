/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityOpen

/-!

# Nearby duality: passing to a larger model

The duality map `δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K` of a trait model over the base
(`NearbyCyclesModel.nearbyDualityMap`) is natural in `K`
(`CategoryTheory.Verdier.map_pre_comp_nearbyDualityMap`), so its invertibility only depends on
the isomorphism class of `K` (`NearbyCyclesModel.isIso_nearbyDualityMap_of_iso`).

If `M` is an open sub-model of a trait model `M̄` over the base, over open immersions
`j : X ⟶ X̄` and `j' : X' ⟶ X̄'` (an open immersion of total spaces compatible with the structure
morphisms, with cartesian square of geometric generic fibres), then Gabber's theorem for `M̄`
implies it for `M` (`NearbyCyclesModel.isIso_nearbyDualityMap_of_openSubmodel`): the restriction
of `δ_{M̄, j_! K}` to `X'` is identified with `δ_{M, j^* j_! K}`
(`NearbyCyclesModel.isIso_map_nearbyDualityMap_iff_of_isOpenImmersion`) and `j^* j_! K ≅ K`.
This is the step "open locality allows a compactification and extension by zero" of the proof of
blueprint `sk-prop-tf-nearby-duality-foundation`, for compactifications by trait models over the
base.

A compactification of an affine total space over the trait
(`NearbyCyclesModel.exists_isProper_openImmersion_of_isAffine`) is in general not a trait model
over the base: its geometric generic fibre need not be open in `X̄ ×_k Spec Ω` for a proper
`k`-scheme `X̄` through which the identification factors. Producing such a compactification needs
gluing `𝒳` with `X̄ ×_k η` along `𝒳_η` and a relative Nagata compactification over `X̄ ×_k S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

variable {Xc : Over (Spec (.of k))} [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom]
  [IsSeparated Xc.hom] {Xc' : Over (Spec (.of k'))} [LocallyOfFiniteType Xc'.hom]
  [QuasiCompact Xc'.hom] [IsSeparated Xc'.hom] {Mc : NearbyCyclesModel Xc.left Xc'.left}
  {qc : Mc.total ⟶ trait k'} {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
