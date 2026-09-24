/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.OECoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization

/-!

# Derived complete objects with coefficients in an `ℓ`-adic field

Let `E` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. This file passes from
the category `D_comp(J, 𝒪_E)` of derived complete objects of the derived category of
sheaves of `𝒪_E`-modules on a site `(C, J)`
(`WeilConjectures.CategoryTheory.DerivedCategory.Complete.OECoefficient`) to the category
`D_comp(J, E)` with coefficients in `E`.

## Inverting the nonzero elements of `𝒪_E`

`D_comp(J, E)` is the rationalization of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`,

```
  D_comp(J, E)  :=  D_comp(J, 𝒪_E) / (torsion objects),
```

the Verdier quotient of `D_comp(J, 𝒪_E)` by the triangulated subcategory of objects killed
by a nonzero element of `𝒪_E`; equivalently, the localization of `D_comp(J, 𝒪_E)` at the
morphisms whose mapping cone is killed by a nonzero element of `𝒪_E`. It is a triangulated
category, and it is `E`-linear because `E` is the fraction field of `𝒪_E`
(`ValuativeRel.isFractionRing_uLift`).

Since `𝒪_E` is a discrete valuation ring in which `ℓ` is a nonzero element of the maximal
ideal, every nonzero element of `𝒪_E` divides a power of `ℓ`, so an object is killed by a
nonzero element of `𝒪_E` if and only if it is killed by a power of `ℓ`: this is the same
category as `D_comp(J, 𝒪_E)[1/ℓ]`, the case `M = Submonoid.powers ℓ` of the
rationalization. Inverting all nonzero elements keeps `ℓ` out of the type of the category,
as in `WeilConjectures.CategoryTheory.DerivedCategory.Complete.OECoefficient`.

The Verdier quotient needs `D_comp(J, 𝒪_E)` to be triangulated, i.e. the derived complete
objects to form a triangulated subcategory of `D(J, 𝒪_E)`
(`DerivedCategory.isTriangulated_derivedCompleteOE` in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.OECoefficient`); this is currently
`sorry`.

## Main definitions

- `ValuativeRel.algebraULift`, `ValuativeRel.isFractionRing_uLift` : `E` is the fraction
  field of the universe `u + 1` copy `ULift 𝒪[E]` of its ring of integers.
- `DerivedCategoryDerivedCompleteE` : the triangulated, `E`-linear category `D_comp(J, E)`.
- `DerivedCategoryDerivedCompleteE.fromOE` : the localization functor
  `D_comp(J, 𝒪_E) ⥤ D_comp(J, E)`.

-/


@[expose] public section

universe u

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

/-- The category `D_comp(J, E)` of derived complete objects with coefficients in the
`ℓ`-adic field `E`: the rationalization of `D_comp(J, 𝒪_E)` at the nonzero elements of
`𝒪_E`, i.e. its Verdier quotient by the objects killed by a nonzero element of `𝒪_E`.
Since `E = 𝒪_E[1/ℓ]`, this is `D_comp(J, 𝒪_E)[1/ℓ]`. It is triangulated and `E`-linear. -/
@[reducible]
def DerivedCategoryDerivedCompleteE : Type _ :=
  Rationalization (nonZeroDivisors (ULift.{u + 1} 𝒪[E])) (DerivedCategoryDerivedCompleteOE J E)

/-- The `Hom` groups of `D_comp(J, E)` are `E`-vector spaces. -/
noncomputable example : Linear E (DerivedCategoryDerivedCompleteE J E) := inferInstance

example : IsTriangulated (DerivedCategoryDerivedCompleteE J E) := inferInstance

/-- The localization functor `D_comp(J, 𝒪_E) ⥤ D_comp(J, E)`. -/
@[reducible]
noncomputable def DerivedCategoryDerivedCompleteE.fromOE :
    DerivedCategoryDerivedCompleteOE J E ⥤ DerivedCategoryDerivedCompleteE J E :=
  Rationalization.Q _ _

end ECoefficient
