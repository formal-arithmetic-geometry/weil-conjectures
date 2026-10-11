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
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.ContinuousMap

/-!

# The `E`-coefficient derived category as the `𝒪_E`-coefficient one with `ℓ` inverted

Let `X` be a scheme, `ℓ` a prime and `E ⊆ ℚ̄_ℓ` a subfield with ring of integers `𝒪_E`. The
sheaves of rings `𝒪_{E,X}` and `E_X` on `X_proét` of
`WeilConjectures.CategoryTheory.RingObjects.EllAdic` are commutative ring objects of the
closed symmetric monoidal Grothendieck abelian category `Sheaf (ProEt.topology X) Ab` of
abelian pro-étale sheaves, and the inclusion `𝒪_{E,X} ⟶ E_X` is a morphism of ring objects
`φ`. This file states that the derived extension of scalars
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

## Sorried input

* `ProEtale.isLocalization_derivedExtendScalars`: `L(extendScalars φ)` is a localization
  functor for the morphisms with `ℓ`-power-torsion mapping cone.

The remaining `sorry`s are inherited from
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` and
`WeilConjectures.CategoryTheory.RingObjects.Ab`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

/-! ### Abelian pro-étale sheaves -/

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u})

/-- The monoidal structure on abelian pro-étale sheaves is symmetric. -/
noncomputable instance sheafAbSymmetricCategory :
    SymmetricCategory (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  Sheaf.symmetricCategory _ _

/-! ### `E` as `𝒪_E` with `ℓ` inverted -/

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The derived extension of scalars `E ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤ D(Mod_{E_X})` is a
localization functor with respect to the morphisms whose mapping cone is killed by some power
of `ℓ`: the `E`-coefficient derived category is the `𝒪_E`-coefficient one with `ℓ`
inverted. -/
instance isLocalization_derivedExtendScalars :
    (Mod.extendScalars ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (padicIntegersSheafToPadicSubfieldSheaf X ℓ E))).leftDerivedFunctor.IsLocalization
      (Rationalization.W (Submonoid.powers (ℓ : ℤ))
        (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
          ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
            (padicIntegersSheaf X ℓ E))))) :=
  sorry

/-- The `E`-coefficient derived category `D(Mod_{E_X})` is equivalent to the rationalization
of the `𝒪_E`-coefficient derived category `D(Mod_{𝒪_{E,X}})` at the powers of `ℓ`. -/
noncomputable def rationalizationEquivalence :
    Rationalization (Submonoid.powers (ℓ : ℤ))
        (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
          ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
            (padicIntegersSheaf X ℓ E)))) ≌
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (padicSubfieldSheaf X ℓ E))) :=
  Localization.uniq (Rationalization.Q _ _) (Mod.extendScalars
    ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (padicIntegersSheafToPadicSubfieldSheaf X ℓ E))).leftDerivedFunctor
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)

/-- Under `rationalizationEquivalence`, the localization functor to the rationalization
corresponds to the derived extension of scalars `E ⊗ᴸ_{𝒪_E} -`. -/
noncomputable def rationalizationQCompEquivalenceIso :
    Rationalization.Q (Submonoid.powers (ℓ : ℤ)) _ ⋙ (rationalizationEquivalence X ℓ E).functor ≅
      (Mod.extendScalars ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (padicIntegersSheafToPadicSubfieldSheaf X ℓ E))).leftDerivedFunctor :=
  Localization.compUniqFunctor (Rationalization.Q _ _) _
    (Rationalization.W (Submonoid.powers (ℓ : ℤ)) _)

end AlgebraicGeometry.ProEtale
