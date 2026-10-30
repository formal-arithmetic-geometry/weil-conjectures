/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-!
# Lisse `ℓ`-adic sheaves in the condensed model

Through the equivalence `E_X : AdicSheaf ℓ X ≌ Mod_{Λ_X}` of
`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`, with `Λ_X` the condensed coefficient
ring `p_X^* ℚ̄_ℓ`, the constant sheaf `ℚ̄_ℓ,X` corresponds to the regular module `Λ_X`, and lisse
`ℓ`-adic sheaves correspond to locally free module objects, hence constructible ones.

## Main results

- `AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModUnitIso`: `E_X ℚ̄_ℓ,X ≅ Λ_X`.
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isLocallyFree_condensedMod`: the module object of
  a lisse `ℓ`-adic sheaf is locally free.
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isConstructibleModuleObject_condensedMod`: the
  module object of a lisse `ℓ`-adic sheaf is constructible.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

variable (l X) in
/-- The module object over `Λ_X` corresponding to the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` is the
regular module `Λ_X`. -/
noncomputable def adicSheafEquivCondensedModUnitIso :
    (adicSheafEquivCondensedMod l X).functor.obj (AdicSheaf.unit l X) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X) :=
  (Mod.comap (condensedRingObjIsoForgetAb l X).hom).mapIso
      ((weilCoefficientsForgetAb l X).mapModRegularIso (adicConstantSheaf l X)) ≪≫
    (Mod.regularIsoComapRegular (condensedRingObjIsoForgetAb l X).hom).symm

private lemma additive_adicSheafEquivCondensedMod_functor (Y : Scheme.{u}) :
    (adicSheafEquivCondensedMod l Y).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] additive_adicSheafEquivCondensedMod_functor
variable (l X) in
/-- The module object over `Λ_X` corresponding to `ℚ̄_ℓ,Xⁿ` is the free module `Λ_Xⁿ`. -/
noncomputable def adicSheafEquivCondensedModFreeIso (n : ℕ) :
    (adicSheafEquivCondensedMod l X).functor.obj (⨁ fun _ : Fin n ↦ AdicSheaf.unit l X) ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X) n :=
  haveI : PreservesBiproduct (fun _ : Fin n ↦ AdicSheaf.unit l X)
      (adicSheafEquivCondensedMod l X).functor :=
    preservesBiproduct_of_preservesProduct _
  (adicSheafEquivCondensedMod l X).functor.mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ adicSheafEquivCondensedModUnitIso l X

/-- If the pullback `f^* H` of an `ℓ`-adic sheaf is isomorphic to `ℚ̄_ℓ,Vⁿ`, then the pullback
`f^* E_X H` of the corresponding module object is free: `f^* E_X H ≅ E_V f^* H ≅ Λ_Vⁿ`. -/
lemma isFree_upperStar_adicSheafEquivCondensedMod_functor_obj {V : Scheme.{u}} (f : V ⟶ X)
    {H : AdicSheaf l X} {n : ℕ}
    (e : (f)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V) :
    Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) V)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} l) f).obj
        ((adicSheafEquivCondensedMod l X).functor.obj H)) :=
  ⟨n, ⟨((adicUpperStarCompCondensedModIso l f).app H).symm ≪≫
    (adicSheafEquivCondensedMod l V).functor.mapIso e ≪≫
    adicSheafEquivCondensedModFreeIso l V n⟩⟩

/-- **The module object of a lisse `ℓ`-adic sheaf is locally free**: on a trivialising cover
`f : V ⟶ X` of the lisse sheaf `H`, `f^* E_X H ≅ E_V f^* H ≅ E_V ℚ̄_ℓ,Vⁿ ≅ Λ_Vⁿ`. -/
theorem IsAdicLisseSheaf.isLocallyFree_condensedMod {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj H) := by
  obtain ⟨R, hR, h⟩ := hH
  obtain ⟨idx, Z, g, rfl⟩ := R.exists_eq_ofArrows
  let U : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
    { I₀ := idx, X := Z, f := g, mem₀ := hR }
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  refine (isLocallyFree_iff _).2 ⟨U.restrictIndexOfSmall.{u}, fun j ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := h (g _) (.mk (Precoverage.ZeroHypercover.Small.restrictFun U j))
  exact isFree_upperStar_adicSheafEquivCondensedMod_functor_obj _ e

/-- **The module object of a lisse `ℓ`-adic sheaf is constructible**, for the trivial
stratification: it is locally free. -/
theorem IsAdicLisseSheaf.isConstructibleModuleObject_condensedMod {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj H) :=
  hH.isLocallyFree_condensedMod.isConstructibleModuleObject

end AlgebraicGeometry.ProEtale
