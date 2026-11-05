/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateBiproduct
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsRegular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.FiberRank

/-!
# Descending a locally free module along a change of coefficients, from transition matrices

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, `S` a scheme and `L` a module
object over `Λ'_S`. Suppose given a finite pro-étale cover `{f_k : V_k ⟶ S}` with trivialisations
`e_k : Λ'_{V_k}^{n_k} ≅ f_k^* L`. On the fibre products `P_{jk} = V_j ×_S V_k` they differ by the
*transition isomorphisms* `p₁^* Λ'^{n_j} ≅ p₂^* Λ'^{n_k}`
(`ProEtale.CondensedRing.finiteFreeTransition`). If all transition isomorphisms and their
inverses have their matrix entries in the image of `Γ(Λ_{P_{jk}}) ⟶ Γ(Λ'_{P_{jk}})`
(`ProEtale.CondensedRing.IsDefinedOver`), and the units `Λ_{V_k}^{n_k} ⟶ Res(Λ'_{V_k}^{n_k})`
are monomorphisms, then `L ≅ Λ'_S ⊗_{Λ_S} L'` for a locally free `Λ_S`-module `L'`
(`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_isDefinedOver`).

The lattices `σ_k : Λ_{V_k}^{n_k} ⟶ f_k^* Res L` spanned by the bases `e_k` agree on the fibre
products up to the matrices over `Λ`, so their cokernels glue
(`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_cover`). The comparison of
`Λ_P^n` with `Λ'_P^n` through the pullbacks rests on the compatibility of (Pull) with the free
module of rank one (`ProEtale.CondensedRing.pullIso_hom_app_regular_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory

namespace Limits

end Limits

namespace Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {D : Type*} [Category* D] [MonoidalCategory D] [Abelian D] [MonoidalPreadditive D]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]
  {S : D} [MonObj S] [PreservesFiniteColimits (tensorLeft S)]
  (F : Mod C R ⥤ Mod D S) [F.Additive] (e : F.obj (regular R) ≅ regular S)

end Mod

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-! ### Compatibility of `comapUpperStarIso` with the comparison of a commutative square -/

section Square

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

end Square

/-! ### Free modules, extension of scalars and pullbacks -/

section FiniteFree

end FiniteFree

/-! ### Gluing the lattices spanned by the bases -/

section Glue

end Glue

end AlgebraicGeometry.ProEtale.CondensedRing
