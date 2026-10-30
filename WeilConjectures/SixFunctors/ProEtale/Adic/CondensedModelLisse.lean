/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap

/-!
# Lisse `ℓ`-adic sheaves in the condensed model

The equivalence `AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod` between `ℓ`-adic
sheaves and module objects over `Λ_X = p_X^* ℚ̄_ℓ` sends the constant sheaf `ℚ̄_ℓ,X` to
the free module `Λ_X` of rank one, hence finite direct sums of copies of `ℚ̄_ℓ,X` to free
modules of finite rank. With the compatibility with pullbacks, the module object of a lisse
`ℓ`-adic sheaf is locally free, hence constructible.

## Main statements

- `AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModUnitIso`: the image of `ℚ̄_ℓ,X`.
- `AlgebraicGeometry.ProEtale.isLocallyFree_of_isAdicLisseSheaf`,
  `AlgebraicGeometry.ProEtale.isConstructibleModuleObject_of_isAdicLisseSheaf`: the module
  object of a lisse sheaf is locally free, hence constructible.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CondensedRing

variable {l : ℕ} [Fact l.Prime]

variable (l) in
/-- The comparison `AdicSheaf ℓ X ≌ Mod_{Λ_X}` sends the constant `ℓ`-adic sheaf
`ℚ̄_ℓ,X` to the free module `Λ_X` of rank one. -/
noncomputable def adicSheafEquivCondensedModUnitIso (X : Scheme.{u}) :
    (adicSheafEquivCondensedMod l X).functor.obj (AdicSheaf.unit l X) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) X) :=
  (Mod.comap (condensedRingObjIsoForgetAb l X).hom).mapIso
      (Mod.isoMk (Iso.refl _) (by simp [Mod.act])) ≪≫
    (Mod.regularIsoComapRegular (condensedRingObjIsoForgetAb l X).hom).symm

/-- The comparison `AdicSheaf ℓ X ≌ Mod_{Λ_X}` is additive, as is any equivalence of
preadditive categories. -/
instance adicSheafEquivCondensedMod_functor_additive (X : Scheme.{u}) :
    (adicSheafEquivCondensedMod l X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- If the `ℓ`-adic sheaf `f^* H` is a finite direct sum of copies of `ℚ̄_ℓ,V`, then the
pullback `f^* E(H)` of its module object over `Λ_X` is free of finite rank:
`f^* E(H) ≅ E(f^* H) ≅ E(ℚ̄_ℓ,Vⁿ) ≅ Λ_Vⁿ`. -/
lemma isFree_upperStar_adicSheafEquivCondensedMod {V X : Scheme.{u}} (f : V ⟶ X)
    {H : AdicSheaf l X} {n : ℕ}
    (e : (f)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V) :
    Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj l) V)
      ((f)^*⟦Profinite.padicAlgClRingObj l⟧.obj
        ((adicSheafEquivCondensedMod l X).functor.obj H)) :=
  ⟨n, ⟨((adicUpperStarCompCondensedModIso l f).app H).symm ≪≫
    (adicSheafEquivCondensedMod l V).functor.mapIso e ≪≫
    (adicSheafEquivCondensedMod l V).functor.mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ adicSheafEquivCondensedModUnitIso l V⟩⟩

/-- The module object over `Λ_X` of an `ℓ`-adic sheaf which is a finite direct sum of copies of
`ℚ̄_ℓ` over the members of a pro-étale cover is locally free. -/
lemma isLocallyFree_adicSheafEquivCondensedMod_of_cover {X : Scheme.{u}} {H : AdicSheaf l X}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ j, ∃ n : ℕ, Nonempty ((𝒰.f j)^*ᵃ[l].obj H ≅
      ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (𝒰.X j))) :
    IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj H) :=
  (isLocallyFree_iff _).2 ⟨𝒰, fun j ↦
    let ⟨_, ⟨e⟩⟩ := h j
    isFree_upperStar_adicSheafEquivCondensedMod (𝒰.f j) e⟩

/-- The module object over `Λ_X` of a lisse `ℓ`-adic sheaf is locally free: it is free of
finite rank over the members of a trivialising cover
(`AlgebraicGeometry.ProEtale.isFree_upperStar_adicSheafEquivCondensedMod`). -/
theorem isLocallyFree_of_isAdicLisseSheaf {X : Scheme.{u}} {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj H) := by
  obtain ⟨R, hR, h⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  let 𝒰 : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
    { I₀ := ι, X := V, f := f, mem₀ := hR }
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  refine isLocallyFree_adicSheafEquivCondensedMod_of_cover 𝒰.restrictIndexOfSmall.{u}
    fun j ↦ ?_
  let i := Precoverage.ZeroHypercover.Small.restrictFun 𝒰 j
  exact h (f i) (.mk i)

/-- The module object over `Λ_X` of a lisse `ℓ`-adic sheaf is constructible: pro-étale locally
it is a finite free module, by the compatibility of `AdicSheaf ℓ X ≌ Mod_{Λ_X}` with
pullbacks. -/
theorem isConstructibleModuleObject_of_isAdicLisseSheaf {X : Scheme.{u}} {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) X)
      ((adicSheafEquivCondensedMod l X).functor.obj H) :=
  isConstructibleModuleObject_of_isLocallyFinitelyPresented
    (isLocallyFree_of_isAdicLisseSheaf hH).isLocallyFinitelyPresented

end AlgebraicGeometry.ProEtale
