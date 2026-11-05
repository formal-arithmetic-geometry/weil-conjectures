/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing
public import WeilConjectures.SixFunctors.ProEtale.Adic.FreeWeilCoefficients

/-!
# Extension of scalars from `ℤ_ℓ,X`-modules to `ℓ`-adic sheaves

Restriction of scalars `AlgebraicGeometry.ProEtale.AdicSheaf.restrictPadicInt` from `ℓ`-adic
sheaves (sheaves of `ℚ̄_ℓ,X`-modules in sheaves of `ℚ̄_ℓ`-modules) to module objects over `ℤ_ℓ,X`
in abelian sheaves has a left adjoint
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsRestrictAdjunction`):
```
M ↦ ℚ̄_ℓ,X ⊗_{(ℚ̄_ℓ ⊗ ℤ_ℓ,X)^#} (ℚ̄_ℓ ⊗ M)^#.
```
It is built in two steps. The sheafified free `ℚ̄_ℓ`-module functor
`F = CategoryTheory.Sheaf.extendScalarsAb` is a strong monoidal left adjoint of the forgetful
functor `weilCoefficientsForgetAb`, so it sends `ℤ_ℓ,X`-modules to `F(ℤ_ℓ,X)`-modules, left
adjoint to the forgetful functor followed by restriction of scalars along the unit
(`CategoryTheory.Adjunction.mapModAdjunction`). The adjoint `F(ℤ_ℓ,X) ⟶ ℚ̄_ℓ,X` of the inclusion
`ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` is a morphism of commutative ring objects, `F` being braided, and extension of
scalars along it is left adjoint to restriction of scalars
(`CategoryTheory.Mod.extendRestrictAdjunction`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The sheafified free `ℚ̄_ℓ`-module functor from abelian sheaves to sheaves of
`ℚ̄_ℓ`-modules on `X_proét`, left adjoint to `weilCoefficientsForgetAb`. -/
noncomputable abbrev weilCoefficientsFree :
    Sheaf (ProEt.topology X) Ab.{u + 1} ⥤
      Sheaf (ProEt.topology X) (WeilCoefficients.{u} l) :=
  Sheaf.extendScalarsAb (ProEt.topology X) (ULift.{u + 1} (PadicAlgCl l))

/-- The sheafified free `ℚ̄_ℓ`-module functor is left adjoint to the forgetful functor, by a
monoidal adjunction. -/
noncomputable abbrev weilCoefficientsFreeAdjunction :
    weilCoefficientsFree X l ⊣ weilCoefficientsForgetAb l X :=
  Sheaf.extendScalarsAbAdjunction (ProEt.topology X) (ULift.{u + 1} (PadicAlgCl l))

/-- `F(ℤ_ℓ,X)` is a commutative ring object, `F` being braided. -/
instance isCommMonObj_weilCoefficientsFree_obj_padicIntSheaf :
    IsCommMonObj ((weilCoefficientsFree X l).obj
      ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntSheaf X l))) :=
  Functor.isCommMonObj_obj (F := weilCoefficientsFree X l)

end AlgebraicGeometry.ProEtale
