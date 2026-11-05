/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethLocal
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityFiniteSupport
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBase

/-!

# Nearby duality over a generic base

Let `M` be a trait model of an `F`-scheme `X₁` over the generic base `(F, X₁)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase`), over the strictly henselian trait
`S = Spec k'⟦t⟧`, and `D` a family of dualizing maps over generic bases
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`). The **duality map**
(`NearbyCyclesModel.nearbyDualityMapOfGenericBase`)
```
δ_{M,K} : Ψ D_{X₁} K ⟶ D_{X'} Ψ K
```
is the adjoint of `θ_M ∘ Ψ(ev) ∘ μ_Ψ` (`CategoryTheory.Verdier.nearbyDualityMap`), as for trait
models over a base field (`NearbyCyclesModel.nearbyDualityMap`). This file adapts the formal
properties of the latter:
* the restriction of `M` to an open of its total space with quasi-compact inclusion is a trait
  model over the same generic base (`NearbyCyclesModel.IsTraitModelOfGenericBase.restrictOpen`);
* nearby duality and open restriction
  (`NearbyCyclesModel.isIso_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion`,
  `NearbyCyclesModel.isIso_map_map_nearbyDualityMapOfGenericBase_iff_of_isOpenImmersion`);
* nearby duality is local on the total space
  (`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_forall_exists_restrictOpen`);
* invariance under isomorphisms of the coefficients and passing to a larger model
  (`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_iso`,
  `NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_openSubmodel`).

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

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

section Restrict

end Restrict

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

section OpenRestriction

variable {Y₁ : Over (Spec (.of F))} [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom]
  [IsSeparated Y₁.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y₁.left Y'.left}
  {j : Y₁ ⟶ X₁} {j' : Y' ⟶ X'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

end OpenRestriction

variable {Xc : Over (Spec (.of F))} [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom]
  [IsSeparated Xc.hom] {Xc' : Over (Spec (.of k'))} [LocallyOfFiniteType Xc'.hom]
  [QuasiCompact Xc'.hom] [IsSeparated Xc'.hom] {Mc : NearbyCyclesModel Xc.left Xc'.left}
  {qc : Mc.total ⟶ trait k'} {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
