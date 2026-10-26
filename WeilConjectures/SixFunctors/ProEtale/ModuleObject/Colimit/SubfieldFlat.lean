/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteExtend

/-!

# Flatness of the `ℓ`-adic coefficient changes

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ_ℓ` inside `ℚ̄_ℓ` and `X` a scheme. This
file proves that the coefficient changes `E_X ⟶ F_X` and `E_X ⟶ ℚ̄_ℓ,X` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` are flat, so that the
comparisons (Pull) and (Push) of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` are defined on the
unbounded derived categories, and (Pull) is an isomorphism there:

* **(A0.2)** `ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`:
  `F_X` is finite free over `E_X`. An `E`-basis `b₁, …, bₙ` of `F` gives `E̲ⁿ ≅ F̲`,
  `(xᵢ) ↦ ∑ xᵢ bᵢ` (`Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`),
  hence `E_Xⁿ ≅ F_X` (`ProEtale.isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`), and
  the extension of scalars along a finite free algebra is exact
  (`CategoryTheory.Mod.preservesFiniteLimits_extendScalars_of_isIso_biproductDesc`).
* **(A0.2)**
  `ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`:
  `ℚ̄_ℓ,X` is the filtered colimit of the `F_X`, `F ≥ E`
  (`ProEtale.isColimitPadicSubfieldAboveRingObjCocone`), each of which is flat over `E_X`, and
  filtered colimits of abelian sheaves are exact
  (`CategoryTheory.Mod.preservesFiniteLimits_extendScalars_of_isColimit_algCocone`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### Flatness of the coefficient inclusions -/

section Flat

variable (X : Scheme.{u})

/-- **(A0.2)** For finite subextensions `E ≤ F`, the extension of scalars along `E_X ⟶ F_X` is
exact: `F_X` is finite free, in particular flat, over `E_X`. See the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) := by
  obtain ⟨n, b, hb⟩ :=
    Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul.{u} ℓ h
  exact Mod.preservesFiniteLimits_extendScalars_of_isIso_biproductDesc _ _
    (isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul X ℓ h b hb)

/-- **(A0.2)** For a finite subextension `E`, the extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` is
exact: `ℚ̄_ℓ,X` is flat over `E_X`, being a filtered colimit of finite free `E_X`-modules. See
the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
    (E : FiniteIntermediateField ℓ) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)) := by
  have := AB5OfSize_of_univLE.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1})
  exact Mod.preservesFiniteLimits_extendScalars_of_isColimit_algCocone _ _ _ _ _
    (padicSubfieldRingObjMap_comp_padicSubfieldAboveRingObjFunctor_map ℓ E X)
    (fun F ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ F.property)
    (isColimitPadicSubfieldAboveRingObjCocone ℓ E X)
    fun F ↦ preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap ℓ X F.property

end Flat

end CondensedRing

end AlgebraicGeometry.ProEtale
