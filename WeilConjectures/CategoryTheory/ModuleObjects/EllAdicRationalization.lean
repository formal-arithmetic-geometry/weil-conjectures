/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!

# The `E`-coefficient derived category as the `𝒪_E`-coefficient one with `ℓ` inverted

Let `X` be a scheme, `ℓ` a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`) with ring of integers `𝒪_E`. The condensed rings
`𝒪̲_E = Profinite.padicIntegersRingObj ℓ E` and `E̲ = Profinite.continuousMapRingObj E`, for the
norm of `E` restricted from `ℚ̄_ℓ`, pull back along `p_X : X_proét ⟶ *_proét` to the
coefficient ring objects `𝒪_{E,X} = p_X^* 𝒪̲_E` and `E_X = p_X^* E̲` of abelian pro-étale sheaves
on `X` (`ProEtale.condensedRingObj`), and the pullback of the inclusion `𝒪̲_E ⟶ E̲`
(`ProEtale.padicIntegersRingObjToContinuousMapRingObj`) is a morphism of ring objects
`φ : 𝒪_{E,X} ⟶ E_X` (`ProEtale.padicIntegersToPadicSubfield`). This file states
that the derived extension of scalars
```
E ⊗ᴸ_{𝒪_E} - = L(extendScalars φ) : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})
```
of `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` exhibits the
`E`-coefficient derived category as the `𝒪_E`-coefficient one with `ℓ` inverted: it is a
localization functor with respect to the class
`CategoryTheory.Rationalization.W (Submonoid.powers ℓ) D(Mod_{𝒪_{E,X}})` of morphisms whose
mapping cone is killed by some power `ℓⁿ` (`ProEtale.isLocalization_derivedExtendScalars`).
Consequently `D(Mod_{E_X})` is equivalent to the rationalization of `D(Mod_{𝒪_{E,X}})` at the
powers of `ℓ` (`ProEtale.rationalizationEquivalence`), compatibly with the localization
functors (`ProEtale.rationalizationQCompEquivalenceIso`).

Neither description is taken as a definition: `E_X` is defined by its sections, not as
`𝒪_{E,X}[1/ℓ]`, following `WeilConjectures/RefactorInstruction.tex`. Finiteness of `E` is what
makes inverting `ℓ` the right statement: `𝒪_E` is then a discrete valuation ring in which every
nonzero element divides a power of `ℓ`.

## Sorried input

* `ProEtale.isLocalization_derivedExtendScalars`: `L(extendScalars φ)` is a localization
  functor for the morphisms with `ℓ`-power-torsion mapping cone.

The remaining `sorry`s are inherited from
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-! ### The inclusion `𝒪_{E,X} ⟶ E_X` -/

/-- The inclusion `𝒪̲_E ⟶ E̲` of ring objects of condensed abelian groups, for a finite
subextension `E`: the abelian sheaf morphism underlying
`Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing`. -/
noncomputable def padicIntegersRingObjToContinuousMapRingObj :
    Profinite.padicIntegersRingObj.{u} ℓ E.1 ⟶ Profinite.continuousMapRingObj E.1 :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ E.1)

instance : IsMonHom (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E) :=
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing.{u} ℓ E.1)))

/-- The inclusion `𝒪_{E,X} ⟶ E_X` of coefficient ring objects on `X_proét`: the pullback along
`p_X` of the inclusion `𝒪̲_E ⟶ E̲` of condensed rings. It is a morphism of ring objects, `p_X^*`
being monoidal. -/
noncomputable abbrev padicIntegersToPadicSubfield :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E.1) X :=
  (upperStarFromPoint X).map (padicIntegersRingObjToContinuousMapRingObj ℓ E)

/-! ### `E` as `𝒪_E` with `ℓ` inverted -/

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})` is a
localization functor with respect to the morphisms whose mapping cone is killed by some power
of `ℓ`: the `E`-coefficient derived category is the `𝒪_E`-coefficient one with `ℓ`
inverted. -/
instance isLocalization_derivedExtendScalars :
    (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.IsLocalization
      (Rationalization.W (Submonoid.powers (ℓ : ℤ))
        (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))) :=
  sorry

/-- The `E`-coefficient derived category `D(Mod_{E_X})` is equivalent to the rationalization
of the `𝒪_E`-coefficient derived category `D(Mod_{𝒪_{E,X}})` at the powers of `ℓ`. -/
noncomputable def rationalizationEquivalence :
    Rationalization (Submonoid.powers (ℓ : ℤ))
        (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) ≌
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) :=
  Localization.uniq (Rationalization.Q _ _)
    (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)

/-- Under `rationalizationEquivalence`, the localization functor to the rationalization
corresponds to the derived extension of scalars `E ⊗ᴸ_{𝒪_E} -`. -/
noncomputable def rationalizationQCompEquivalenceIso :
    Rationalization.Q (Submonoid.powers (ℓ : ℤ)) _ ⋙ (rationalizationEquivalence X ℓ E).functor ≅
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor :=
  Localization.compUniqFunctor (Rationalization.Q _ _) _
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)

end AlgebraicGeometry.ProEtale
