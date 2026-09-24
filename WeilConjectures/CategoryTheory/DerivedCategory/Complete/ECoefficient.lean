/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.OECoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!

# Derived complete objects with coefficients in an `ℓ`-adic field

Let `E` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. This file passes from
the derived category `D(J, 𝒪_E)` of sheaves of `𝒪_E`-modules on a site `(C, J)`, and its
full subcategory `D_comp(J, 𝒪_E)` of derived complete objects
(`WeilConjectures.CategoryTheory.DerivedCategory.Complete.OECoefficient`), to coefficients
in `E`.

## Inverting the nonzero elements of `𝒪_E`

The category with `E`-coefficients is the rationalization of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`,

```
  D(J, E)  :=  D(J, 𝒪_E) / (torsion objects),
```

the Verdier quotient of `D(J, 𝒪_E)` by the triangulated subcategory of objects killed by a
nonzero element of `𝒪_E`; equivalently, the localization of `D(J, 𝒪_E)` at the morphisms
whose mapping cone is killed by a nonzero element of `𝒪_E`. It is a triangulated category,
and it is `E`-linear because `E` is the fraction field of `𝒪_E`
(`ValuativeRel.isFractionRing_uLift`).

Since `𝒪_E` is a discrete valuation ring in which `ℓ` is a nonzero element of the maximal
ideal, every nonzero element of `𝒪_E` divides a power of `ℓ`, so an object is killed by a
nonzero element of `𝒪_E` if and only if it is killed by a power of `ℓ`: this is the same
category as `D(J, 𝒪_E)[1/ℓ]`, the case `M = Submonoid.powers ℓ` of the rationalization.
Inverting all nonzero elements keeps `ℓ` out of the type of the category, as in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.OECoefficient`.

The category `D_comp(J, E)` is the full subcategory of `D(J, E)` on the images of the
derived complete objects of `D(J, 𝒪_E)`. The rationalization is taken on `D(J, 𝒪_E)`,
rather than on `D_comp(J, 𝒪_E)` itself, because the Verdier quotient needs a triangulated
category, and closure of the derived complete objects under shifts and cones is not
established here.

## Main definitions

- `ValuativeRel.algebraULift`, `ValuativeRel.isFractionRing_uLift` : `E` is the fraction
  field of the universe `u + 1` copy `ULift 𝒪[E]` of its ring of integers.
- `DerivedCategoryE` : the triangulated, `E`-linear category `D(J, E)`.
- `DerivedCategoryE.fromOE` : the localization functor `D(J, 𝒪_E) ⥤ D(J, E)`.
- `DerivedCategory.derivedCompleteE` : the essential image in `D(J, E)` of the derived
  complete objects of `D(J, 𝒪_E)`.
- `DerivedCategoryDerivedCompleteE` : the `E`-linear category `D_comp(J, E)`, with its
  inclusion `DerivedCategoryDerivedCompleteE.ι` into `D(J, E)` and the functor
  `DerivedCategoryDerivedCompleteE.fromOE` from `D_comp(J, 𝒪_E)`.

-/

@[expose] public section

universe uA u

open CategoryTheory Limits ValuativeRel

section RingOfIntegers

variable (E : Type) [Field E] [ValuativeRel E]

/-- `E` as an algebra over the universe `u + 1` copy `ULift 𝒪[E]` of its ring of integers.
The scalar action is the one of `ULift.module`, `r • x = r.down • x`. -/
noncomputable instance ValuativeRel.algebraULift : Algebra (ULift.{u + 1} 𝒪[E]) E where
  algebraMap := (algebraMap 𝒪[E] E).comp (ValuativeRel.uliftRingEquiv.{u} E).symm.toRingHom
  commutes' _ _ := mul_comm _ _
  smul_def' r x := Algebra.smul_def r.down x

/-- `E` is the fraction field of the universe `u + 1` copy `ULift 𝒪[E]` of its ring of
integers, as it is of `𝒪[E]` itself. -/
instance ValuativeRel.isFractionRing_uLift : IsFractionRing (ULift.{u + 1} 𝒪[E]) E :=
  IsFractionRing.of_ringEquiv_left (ValuativeRel.uliftRingEquiv.{u} E).symm fun _ ↦ rfl

end RingOfIntegers

section ECoefficient

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (E : Type) [Field E] [ValuativeRel E]

/-- The derived category `D(J, E)` of sheaves with coefficients in the `ℓ`-adic field `E`:
the rationalization of the derived category `D(J, 𝒪_E)` of sheaves of `𝒪_E`-modules at the
nonzero elements of `𝒪_E`, i.e. its Verdier quotient by the objects killed by a nonzero
element of `𝒪_E`. Since `E = 𝒪_E[1/ℓ]`, this is `D(J, 𝒪_E)[1/ℓ]`. It is triangulated
and `E`-linear. -/
@[reducible]
def DerivedCategoryE : Type _ :=
  Rationalization (nonZeroDivisors (ULift.{u + 1} 𝒪[E]))
    (DerivedCategory (Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} 𝒪[E]))))

/-- The `Hom` groups of `D(J, E)` are `E`-vector spaces. -/
noncomputable example : Linear E (DerivedCategoryE J E) := inferInstance

example : IsTriangulated (DerivedCategoryE J E) := inferInstance

/-- The localization functor `D(J, 𝒪_E) ⥤ D(J, E)`. -/
@[reducible]
noncomputable def DerivedCategoryE.fromOE :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} 𝒪[E]))) ⥤
      DerivedCategoryE J E :=
  Rationalization.Q _ _

/-- An object of `D(J, E)` is *derived complete* if it is isomorphic to the image of a
derived complete object of `D(J, 𝒪_E)` (`DerivedCategory.derivedCompleteOE`). -/
noncomputable def DerivedCategory.derivedCompleteE : ObjectProperty (DerivedCategoryE J E) :=
  (DerivedCategory.derivedCompleteOE J E).map (DerivedCategoryE.fromOE J E)

/-- The category `D_comp(J, E)` of derived complete objects with coefficients in the
`ℓ`-adic field `E`: the full subcategory of `D(J, E)` on the images of the derived complete
objects of `D(J, 𝒪_E)`. -/
noncomputable def DerivedCategoryDerivedCompleteE : Type _ :=
  (DerivedCategory.derivedCompleteE J E).FullSubcategory

noncomputable instance : Category (DerivedCategoryDerivedCompleteE J E) :=
  inferInstanceAs <| Category (DerivedCategory.derivedCompleteE J E).FullSubcategory

noncomputable instance : Preadditive (DerivedCategoryDerivedCompleteE J E) :=
  inferInstanceAs <| Preadditive (DerivedCategory.derivedCompleteE J E).FullSubcategory

/-- The `Hom` groups of `D_comp(J, E)` are `E`-vector spaces. -/
noncomputable instance : Linear E (DerivedCategoryDerivedCompleteE J E) :=
  inferInstanceAs <| Linear E (DerivedCategory.derivedCompleteE J E).FullSubcategory

/-- The inclusion of `D_comp(J, E)` into `D(J, E)`. -/
noncomputable def DerivedCategoryDerivedCompleteE.ι :
    DerivedCategoryDerivedCompleteE J E ⥤ DerivedCategoryE J E :=
  (DerivedCategory.derivedCompleteE J E).ι

/-- The functor `D_comp(J, 𝒪_E) ⥤ D_comp(J, E)`, the restriction of the localization
functor `DerivedCategoryE.fromOE`. -/
noncomputable def DerivedCategoryDerivedCompleteE.fromOE :
    DerivedCategoryDerivedCompleteOE J E ⥤ DerivedCategoryDerivedCompleteE J E :=
  (DerivedCategory.derivedCompleteE J E).lift
    (DerivedCategoryDerivedCompleteOE.ι J E ⋙ DerivedCategoryE.fromOE J E)
    fun K ↦ ObjectProperty.prop_map_obj _ _ K.property

end ECoefficient
