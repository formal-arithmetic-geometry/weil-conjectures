/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient

/-!
# Extension of scalars between rings of integers of `ℓ`-adic fields

Let `ℚ̄_ℓ / F / E / ℚ_ℓ` be a tower of fields, with `F` and `E` embedded in the fixed algebraic
closure `ℚ̄_ℓ = PadicAlgCl l` compatibly. This file constructs the transition functor

```
  - ⊗_{𝒪_E} 𝒪_F : D(X, 𝒪_E) ⥤ D(X, 𝒪_F)
```

between the derived categories of sheaves of modules over the rings of integers on the small
pro-étale site of a scheme `X`, as a preparation for the `ℚ̄_ℓ`-coefficient derived category.
`F` is not assumed finite over `E`, so that it may be taken to be `ℚ̄_ℓ` itself.

## Flatness

The inclusion `𝒪_E → 𝒪_F` is injective and `𝒪_F` is a domain, so `𝒪_F` is a torsion free
`𝒪_E`-module; since `𝒪_E` is a valuation ring, hence a Bézout domain, it is flat
(`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`). Consequently the extension of scalars
of sheaves `Sheaf.algebraExtendScalars` of
`WeilConjectures.CategoryTheory.DerivedCategory.ChangeOfRings` is exact, and the functor on
derived categories is directly its levelwise application `Functor.mapDerivedCategory`, with
no need to derive it.

## Constructible objects

When `E` is finite over `ℚ_ℓ` and `F` is finite over `E`, the functor sends constructible
objects to constructible objects, hence restricts to a functor
`D_cons(X, 𝒪_E) ⥤ D_cons(X, 𝒪_F)` between the full subcategories of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient`. The three
conditions of [Stacks 09C1] are treated in three separate statements, each currently
`sorry`.

## Rational coefficients

The functor `D_cons(X, 𝒪_E) ⥤ D_cons(X, 𝒪_F)` is triangulated and sends objects killed by a
nonzero element of `𝒪_E` to objects killed by a nonzero element of `𝒪_F` (currently
`sorry`), so it sends morphisms with torsion mapping cone to morphisms with torsion mapping
cone. Hence its composition with the localization `D_cons(X, 𝒪_F) ⥤ D_cons(X, F)` factors
uniquely through the localization `D_cons(X, 𝒪_E) ⥤ D_cons(X, E)`
(`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient`), giving the
extension of scalars `- ⊗_E F : D_cons(X, E) ⥤ D_cons(X, F)`.

## Extension of scalars to `ℚ̄_ℓ`

Similarly, `ℚ̄_ℓ` is a torsion free, hence flat, `𝒪_E`-module, so the extension of scalars
along `𝒪_E → ℚ̄_ℓ` gives an exact functor `D(X, 𝒪_E) ⥤ D(X, ℚ̄_ℓ)` to the derived category of
pro-étale sheaves of modules over `ℚ̄_ℓ` with its discrete topology. Restricted to
`D_cons(X, 𝒪_E)`, it kills the objects killed by a nonzero element of `𝒪_E` (currently
`sorry`), as these act invertibly on `ℚ̄_ℓ`; so it sends morphisms with torsion mapping cone
to isomorphisms, and factors uniquely through the localization `D_cons(X, 𝒪_E) ⥤ D_cons(X, E)`,
giving `- ⊗_E ℚ̄_ℓ : D_cons(X, E) ⥤ D(X, ℚ̄_ℓ)`.

## Main definitions

- `PadicAlgCl.integersMap` : the inclusion `𝒪_E → 𝒪_F` of rings of integers.
- `PadicAlgCl.algebraShrinkIntegers` : the induced algebra structure between the universe
  `u + 1` copies `Shrink 𝒪_E` and `Shrink 𝒪_F`, a local instance in this file.
- `DerivedCategory.integralExtendScalars` : the functor `D(X, 𝒪_E) ⥤ D(X, 𝒪_F)`.
- `DerivedCategoryConstructibleIntegral.extendScalars` : its restriction
  `D_cons(X, 𝒪_E) ⥤ D_cons(X, 𝒪_F)` for `F` finite over `E`.
- `DerivedCategoryConstructibleRational.extendScalars` : the induced functor
  `D_cons(X, E) ⥤ D_cons(X, F)` on the rationalizations, for `F` finite over `E`.
- `PadicAlgCl.algebraShrinkIntegersShrink` : the algebra structure of `Shrink ℚ̄_ℓ` over
  `Shrink 𝒪_E`.
- `DerivedCategory.integralExtendScalarsQlbar` : the functor `D(X, 𝒪_E) ⥤ D(X, ℚ̄_ℓ)`.
- `DerivedCategoryConstructibleIntegral.extendScalarsQlbar` : its restriction
  `D_cons(X, 𝒪_E) ⥤ D(X, ℚ̄_ℓ)`.
- `DerivedCategoryConstructibleRational.extendScalarsQlbar` : the induced functor
  `D_cons(X, E) ⥤ D(X, ℚ̄_ℓ)`.
- `DerivedCategory.integralExtendScalarsComp`,
  `DerivedCategory.integralExtendScalarsQlbarComp` : for a tower `E → F → G`, the extension of
  scalars along `𝒪_E → 𝒪_G` (resp. `𝒪_E → ℚ̄_ℓ`) is the composite of those along
  `𝒪_E → 𝒪_F` and `𝒪_F → 𝒪_G` (resp. `𝒪_F → ℚ̄_ℓ`), induced by
  `Sheaf.algebraExtendScalarsComp` through `Functor.mapDerivedCategoryNatIso` and
  `Functor.mapDerivedCategoryCompIso`.
- `DerivedCategoryConstructibleIntegral.extendScalarsComp`,
  `DerivedCategoryConstructibleIntegral.extendScalarsQlbarComp` : their restrictions to
  `D_cons(X, 𝒪_E)`.
- `DerivedCategoryConstructibleRational.extendScalarsComp`,
  `DerivedCategoryConstructibleRational.extendScalarsQlbarComp` : the corresponding
  isomorphisms on `D_cons(X, E)`, descended along the localization functor, precomposition
  with which is fully faithful.

## Main results

- `PadicAlgCl.flat_algebraMap_shrinkIntegers` : `Shrink 𝒪_F` is flat over `Shrink 𝒪_E`.
- `DerivedCategory.derivedCompleteIntegral_le_inverseImage_integralExtendScalars`,
  `DerivedCategory.constructibleHomology_le_inverseImage_integralExtendScalars`,
  `DerivedCategory.locallyFiniteTorDimension_le_inverseImage_integralExtendScalars` : the
  functor preserves each of the three conditions defining constructible objects (`sorry`).
- `DerivedCategory.constructibleIntegral_le_inverseImage_integralExtendScalars` : the functor
  preserves constructible objects.
- `DerivedCategoryConstructibleIntegral.torsion_le_inverseImage_extendScalars` : the functor
  sends objects killed by a nonzero element of `𝒪_E` to objects killed by a nonzero element
  of `𝒪_F` (`sorry`).
- `DerivedCategoryConstructibleRational.isInvertedBy_extendScalars` : consequently the
  functor inverts, after localization, the morphisms inverted in `D_cons(X, E)`.
- `PadicAlgCl.flat_algebraMap_shrinkIntegers_shrink` : `Shrink ℚ̄_ℓ` is flat over
  `Shrink 𝒪_E`.
- `DerivedCategoryConstructibleIntegral.isZero_extendScalarsQlbar_obj_of_torsion` : the
  functor `D_cons(X, 𝒪_E) ⥤ D(X, ℚ̄_ℓ)` kills torsion objects (`sorry`).
- `DerivedCategoryConstructibleRational.isInvertedBy_extendScalarsQlbar` : consequently it
  inverts the morphisms inverted in `D_cons(X, E)`.
-/

@[expose] public section

universe w w' w'' u

open AlgebraicGeometry CategoryTheory IsLocalRing Limits

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  (F : Type w') [Field F] [Algebra F (PadicAlgCl l)] [Algebra E F]
  [IsScalarTower E F (PadicAlgCl l)]

/-- The inclusion `𝒪_E → 𝒪_F` of rings of integers induced by `E → F`: an element of `E`
of norm at most `1` in `ℚ̄_ℓ` is sent to an element of `F` of the same norm. -/
noncomputable def integersMap : integers l E →+* integers l F :=
  (algebraMap E F).restrict (integers l E) (integers l F) fun x hx ↦ by
    rw [mem_integers_iff] at hx ⊢
    rwa [← IsScalarTower.algebraMap_apply]

lemma integersMap_injective : Function.Injective (integersMap l E F) := fun _ _ h ↦
  Subtype.ext ((algebraMap E F).injective (congrArg Subtype.val h))

/-- `𝒪_F` is flat over `𝒪_E`: it is a torsion free module over the Bézout domain `𝒪_E`. -/
lemma flat_integersMap : (integersMap l E F).Flat := by
  algebraize [integersMap l E F]
  rw [RingHom.Flat, Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr (integersMap_injective l E F)

variable [Small.{u + 1} E] [Small.{u + 1} F]

/-- The algebra structure of `Shrink 𝒪_F` over `Shrink 𝒪_E`, transported from
`PadicAlgCl.integersMap` along `PadicAlgCl.shrinkRingEquiv`. It is not an instance, as for
`F = E` it would compete with `Algebra.id`. -/
noncomputable abbrev algebraShrinkIntegers :
    Algebra (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l F)) :=
  ((shrinkRingEquiv l F).toRingHom.comp
    ((integersMap l E F).comp (shrinkRingEquiv l E).symm.toRingHom)).toAlgebra

attribute [local instance] algebraShrinkIntegers

/-- `Shrink 𝒪_F` is flat over `Shrink 𝒪_E`, as `𝒪_F` is over `𝒪_E`. -/
lemma flat_algebraMap_shrinkIntegers :
    (algebraMap (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l F))).Flat :=
  ((RingHom.Flat.of_bijective (shrinkRingEquiv l E).symm.bijective).comp
    (flat_integersMap l E F)).comp (RingHom.Flat.of_bijective (shrinkRingEquiv l F).bijective)

end PadicAlgCl

section ExtendScalars

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Small.{u + 1} E]
  (F : Type w') [Field F] [Algebra F (PadicAlgCl l)] [Small.{u + 1} F] [Algebra E F]
  [IsScalarTower E F (PadicAlgCl l)]

attribute [local instance] PadicAlgCl.algebraShrinkIntegers

/-- The extension of scalars of sheaves of modules along a flat algebra `R → S` is left
exact: it is sectionwise left exact by flatness, and sheafification is exact. -/
lemma Sheaf.preservesFiniteLimits_algebraExtendScalars_of_flat (R S : Type (u + 1))
    [CommRing R] [CommRing S] [Algebra R S] (h : (algebraMap R S).Flat) :
    PreservesFiniteLimits (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X) R S) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat.{u + 1} h
  have : PreservesFiniteLimits (ModuleCat.algebraExtendScalars.{u + 1} R S) :=
    preservesFiniteLimits_of_natIso (Adjunction.leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj.{u + 1} _)
      (ModuleCat.algebraExtendRestrictScalarsAdj _ _))
  have : PreservesFiniteLimits ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
      (ModuleCat.algebraExtendScalars.{u + 1} R S)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  dsimp only [Sheaf.algebraExtendScalars, Sheaf.composeAndSheafify]
  infer_instance

/-- The extension of scalars of sheaves of modules along the flat `Shrink 𝒪_E → Shrink 𝒪_F`
is left exact. -/
instance Sheaf.preservesFiniteLimits_algebraExtendScalars_shrinkIntegers :
    PreservesFiniteLimits (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X)
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) (Shrink.{u + 1} (PadicAlgCl.integers l F))) :=
  Sheaf.preservesFiniteLimits_algebraExtendScalars_of_flat X _ _
    (PadicAlgCl.flat_algebraMap_shrinkIntegers l E F)

/-- The extension of scalars `- ⊗_{𝒪_E} 𝒪_F : D(X, 𝒪_E) ⥤ D(X, 𝒪_F)` on the derived
categories of pro-étale sheaves of modules over the rings of integers. As `𝒪_F` is flat over
`𝒪_E`, the extension of scalars of sheaves is exact, and this is the functor it induces
levelwise. -/
noncomputable def DerivedCategory.integralExtendScalars :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l F)))) :=
  (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X)
    (Shrink.{u + 1} (PadicAlgCl.integers l E))
      (Shrink.{u + 1} (PadicAlgCl.integers l F))).mapDerivedCategory

noncomputable instance : (DerivedCategory.integralExtendScalars X l E F).CommShift ℤ :=
  inferInstanceAs <| (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X)
    (Shrink.{u + 1} (PadicAlgCl.integers l E))
      (Shrink.{u + 1} (PadicAlgCl.integers l F))).mapDerivedCategory.CommShift ℤ

instance : (DerivedCategory.integralExtendScalars X l E F).IsTriangulated :=
  inferInstanceAs <| (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X)
    (Shrink.{u + 1} (PadicAlgCl.integers l E))
      (Shrink.{u + 1} (PadicAlgCl.integers l F))).mapDerivedCategory.IsTriangulated

end ExtendScalars

section Constructible

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Small.{u + 1} E] [Algebra ℚ_[l] E]
  [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  (F : Type w') [Field F] [Algebra F (PadicAlgCl l)] [Small.{u + 1} F] [Algebra E F]
  [IsScalarTower E F (PadicAlgCl l)] [FiniteDimensional E F]

namespace DerivedCategory

/-- For `F` finite over `E`, the extension of scalars `- ⊗_{𝒪_E} 𝒪_F` sends derived complete
objects to derived complete objects. -/
lemma derivedCompleteIntegral_le_inverseImage_integralExtendScalars :
    derivedCompleteIntegral X l E ≤
      (derivedCompleteIntegral X l F).inverseImage (integralExtendScalars X l E F) :=
  sorry

/-- For `F` finite over `E`, if the reduction `K ⊗ᴸ_{𝒪_E} 𝒪_E/𝔪_E` has constructible
homology sheaves, so does the reduction `(K ⊗_{𝒪_E} 𝒪_F) ⊗ᴸ_{𝒪_F} 𝒪_F/𝔪_F`. -/
lemma constructibleHomology_le_inverseImage_integralExtendScalars :
    (ProEtale.DerivedCategory.constructibleHomology
        (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
          maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l E))) X).inverseImage
      (algebraExtendScalars (Scheme.ProEt.topology X) _ _) ≤
    ((ProEtale.DerivedCategory.constructibleHomology
        (Shrink.{u + 1} (PadicAlgCl.integers l F) ⧸
          maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l F))) X).inverseImage
      (algebraExtendScalars (Scheme.ProEt.topology X) _ _)).inverseImage
      (integralExtendScalars X l E F) :=
  sorry

/-- For `F` finite over `E`, if the reduction `K ⊗ᴸ_{𝒪_E} 𝒪_E/𝔪_E` locally has finite tor
dimension, so does the reduction `(K ⊗_{𝒪_E} 𝒪_F) ⊗ᴸ_{𝒪_F} 𝒪_F/𝔪_F`. -/
lemma locallyFiniteTorDimension_le_inverseImage_integralExtendScalars :
    (locallyFiniteTorDimension (Scheme.ProEt.topology X)
        (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
          maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l E)))).inverseImage
      (algebraExtendScalars (Scheme.ProEt.topology X) _ _) ≤
    ((locallyFiniteTorDimension (Scheme.ProEt.topology X)
        (Shrink.{u + 1} (PadicAlgCl.integers l F) ⧸
          maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l F)))).inverseImage
      (algebraExtendScalars (Scheme.ProEt.topology X) _ _)).inverseImage
      (integralExtendScalars X l E F) :=
  sorry

/-- For `F` finite over `E`, the extension of scalars `- ⊗_{𝒪_E} 𝒪_F` sends constructible
objects to constructible objects, by the three statements above. -/
lemma constructibleIntegral_le_inverseImage_integralExtendScalars :
    constructibleIntegral X l E ≤
      (constructibleIntegral X l F).inverseImage (integralExtendScalars X l E F) :=
  fun _ ⟨h₁, h₂, h₃⟩ ↦
    ⟨derivedCompleteIntegral_le_inverseImage_integralExtendScalars X l E F _ h₁,
      constructibleHomology_le_inverseImage_integralExtendScalars X l E F _ h₂,
      locallyFiniteTorDimension_le_inverseImage_integralExtendScalars X l E F _ h₃⟩

end DerivedCategory

/-- For `F` finite over `E`, the extension of scalars `D_cons(X, 𝒪_E) ⥤ D_cons(X, 𝒪_F)`:
the restriction of `DerivedCategory.integralExtendScalars` to the full subcategories of
constructible objects. -/
noncomputable def DerivedCategoryConstructibleIntegral.extendScalars :
    DerivedCategoryConstructibleIntegral X l E ⥤ DerivedCategoryConstructibleIntegral X l F :=
  ObjectProperty.lift _ (DerivedCategoryConstructibleIntegral.ι X l E ⋙
      DerivedCategory.integralExtendScalars X l E F)
    fun K ↦ DerivedCategory.constructibleIntegral_le_inverseImage_integralExtendScalars
      X l E F _ K.property

noncomputable instance :
    (DerivedCategoryConstructibleIntegral.extendScalars X l E F).CommShift ℤ :=
  inferInstanceAs <| (ObjectProperty.lift _ (DerivedCategoryConstructibleIntegral.ι X l E ⋙
      DerivedCategory.integralExtendScalars X l E F)
    fun K ↦ DerivedCategory.constructibleIntegral_le_inverseImage_integralExtendScalars
      X l E F _ K.property).CommShift ℤ

instance : (DerivedCategoryConstructibleIntegral.extendScalars X l E F).IsTriangulated :=
  inferInstanceAs <| (ObjectProperty.lift _ (DerivedCategoryConstructibleIntegral.ι X l E ⋙
      DerivedCategory.integralExtendScalars X l E F)
    fun K ↦ DerivedCategory.constructibleIntegral_le_inverseImage_integralExtendScalars
      X l E F _ K.property).IsTriangulated

/-- For `F` finite over `E`, the extension of scalars `D_cons(X, 𝒪_E) ⥤ D_cons(X, 𝒪_F)` sends
objects killed by a nonzero element of `𝒪_E` to objects killed by a nonzero element of `𝒪_F`:
if `m • 𝟙 K = 0`, then the image of `m` in `𝒪_F`, which is nonzero, kills `K ⊗_{𝒪_E} 𝒪_F`. -/
lemma DerivedCategoryConstructibleIntegral.torsion_le_inverseImage_extendScalars :
    Rationalization.torsion (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryConstructibleIntegral X l E) ≤
      (Rationalization.torsion (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l F)))
        (DerivedCategoryConstructibleIntegral X l F)).inverseImage
        (DerivedCategoryConstructibleIntegral.extendScalars X l E F) :=
  sorry

/-- For `F` finite over `E`, the morphisms of `D_cons(X, 𝒪_E)` inverted in `D_cons(X, E)` are
sent to isomorphisms of `D_cons(X, F)` by the extension of scalars followed by the
localization functor: their mapping cones are torsion, hence so are the mapping cones of
their images, as the extension of scalars is triangulated and preserves torsion objects. -/
lemma DerivedCategoryConstructibleRational.isInvertedBy_extendScalars :
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryConstructibleIntegral X l E)).IsInvertedBy
      (DerivedCategoryConstructibleIntegral.extendScalars X l E F ⋙
        DerivedCategoryConstructibleRational.fromIntegral X l F) := fun _ _ f hf ↦
  ObjectProperty.inverseImage_trW_isInverted _ _ _ f
    (ObjectProperty.trW_monotone
      (DerivedCategoryConstructibleIntegral.torsion_le_inverseImage_extendScalars X l E F) _ hf)

/-- For `F` finite over `E`, the extension of scalars `D_cons(X, E) ⥤ D_cons(X, F)`: the
functor induced on the rationalizations by
`DerivedCategoryConstructibleIntegral.extendScalars`, through the universal property of the
localization `D_cons(X, 𝒪_E) ⥤ D_cons(X, E)`. -/
noncomputable def DerivedCategoryConstructibleRational.extendScalars :
    DerivedCategoryConstructibleRational X l E ⥤ DerivedCategoryConstructibleRational X l F :=
  Localization.lift (DerivedCategoryConstructibleIntegral.extendScalars X l E F ⋙
      DerivedCategoryConstructibleRational.fromIntegral X l F)
    (DerivedCategoryConstructibleRational.isInvertedBy_extendScalars X l E F)
    (DerivedCategoryConstructibleRational.fromIntegral X l E)

/-- The extension of scalars on `D_cons(X, E)` is compatible with the one on
`D_cons(X, 𝒪_E)` through the localization functors. -/
noncomputable def DerivedCategoryConstructibleRational.fromIntegralCompExtendScalarsIso :
    DerivedCategoryConstructibleRational.fromIntegral X l E ⋙
        DerivedCategoryConstructibleRational.extendScalars X l E F ≅
      DerivedCategoryConstructibleIntegral.extendScalars X l E F ⋙
        DerivedCategoryConstructibleRational.fromIntegral X l F :=
  Localization.fac _ _ _

end Constructible

section Qlbar

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]

/-- `ℚ̄_ℓ` is flat over `𝒪_E`: it is a torsion free module over the Bézout domain `𝒪_E`. -/
lemma flat_algebraMap_integers :
    (algebraMap (integers l E) (PadicAlgCl l)).Flat := by
  rw [RingHom.flat_algebraMap_iff, Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr
    ((algebraMap E (PadicAlgCl l)).injective.comp Subtype.val_injective)

/-- The identification of `ℚ̄_ℓ` with its copy `Shrink ℚ̄_ℓ` in the universe `u + 1`. -/
noncomputable def shrinkRingEquivSelf : PadicAlgCl l ≃+* Shrink.{u + 1} (PadicAlgCl l) :=
  (Shrink.ringEquiv.{u + 1} (PadicAlgCl l)).symm

variable [Small.{u + 1} E]

/-- The algebra structure of `Shrink ℚ̄_ℓ` over `Shrink 𝒪_E`, transported from the inclusion
`𝒪_E → ℚ̄_ℓ` along `PadicAlgCl.shrinkRingEquiv` and `PadicAlgCl.shrinkRingEquivSelf`. -/
noncomputable instance algebraShrinkIntegersShrink :
    Algebra (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (PadicAlgCl l)) :=
  ((shrinkRingEquivSelf.{u} l).toRingHom.comp
    ((algebraMap (integers l E) (PadicAlgCl l)).comp
      (shrinkRingEquiv l E).symm.toRingHom)).toAlgebra

/-- `Shrink ℚ̄_ℓ` is flat over `Shrink 𝒪_E`, as `ℚ̄_ℓ` is over `𝒪_E`. -/
lemma flat_algebraMap_shrinkIntegers_shrink :
    (algebraMap (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (PadicAlgCl l))).Flat :=
  ((RingHom.Flat.of_bijective (shrinkRingEquiv l E).symm.bijective).comp
    (flat_algebraMap_integers l E)).comp
      (RingHom.Flat.of_bijective (shrinkRingEquivSelf.{u} l).bijective)

end PadicAlgCl

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Small.{u + 1} E]

/-- The extension of scalars of sheaves of modules along the flat `Shrink 𝒪_E → Shrink ℚ̄_ℓ`
is left exact. -/
instance Sheaf.preservesFiniteLimits_algebraExtendScalars_shrinkIntegers_shrink :
    PreservesFiniteLimits (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X)
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) (Shrink.{u + 1} (PadicAlgCl l))) :=
  Sheaf.preservesFiniteLimits_algebraExtendScalars_of_flat X _ _
    (PadicAlgCl.flat_algebraMap_shrinkIntegers_shrink l E)

/-- The extension of scalars `- ⊗_{𝒪_E} ℚ̄_ℓ : D(X, 𝒪_E) ⥤ D(X, ℚ̄_ℓ)` to the derived category
of pro-étale sheaves of modules over `ℚ̄_ℓ` with its discrete topology. As `ℚ̄_ℓ` is flat over
`𝒪_E`, the extension of scalars of sheaves is exact, and this is the functor it induces
levelwise. -/
noncomputable def DerivedCategory.integralExtendScalarsQlbar :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl l)))) :=
  (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X)
    (Shrink.{u + 1} (PadicAlgCl.integers l E)) (Shrink.{u + 1} (PadicAlgCl l))).mapDerivedCategory

noncomputable instance : (DerivedCategory.integralExtendScalarsQlbar X l E).CommShift ℤ :=
  inferInstanceAs <| (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X)
    (Shrink.{u + 1} (PadicAlgCl.integers l E))
      (Shrink.{u + 1} (PadicAlgCl l))).mapDerivedCategory.CommShift ℤ

instance : (DerivedCategory.integralExtendScalarsQlbar X l E).IsTriangulated :=
  inferInstanceAs <| (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X)
    (Shrink.{u + 1} (PadicAlgCl.integers l E))
      (Shrink.{u + 1} (PadicAlgCl l))).mapDerivedCategory.IsTriangulated

/-- The extension of scalars `D_cons(X, 𝒪_E) ⥤ D(X, ℚ̄_ℓ)`: the restriction of
`DerivedCategory.integralExtendScalarsQlbar` to the constructible objects. -/
noncomputable def DerivedCategoryConstructibleIntegral.extendScalarsQlbar :
    DerivedCategoryConstructibleIntegral X l E ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl l)))) :=
  DerivedCategoryConstructibleIntegral.ι X l E ⋙ DerivedCategory.integralExtendScalarsQlbar X l E

noncomputable instance :
    (DerivedCategoryConstructibleIntegral.extendScalarsQlbar X l E).CommShift ℤ :=
  inferInstanceAs <| (DerivedCategoryConstructibleIntegral.ι X l E ⋙
    DerivedCategory.integralExtendScalarsQlbar X l E).CommShift ℤ

instance : (DerivedCategoryConstructibleIntegral.extendScalarsQlbar X l E).IsTriangulated :=
  inferInstanceAs <| (DerivedCategoryConstructibleIntegral.ι X l E ⋙
    DerivedCategory.integralExtendScalarsQlbar X l E).IsTriangulated

/-- The extension of scalars `D_cons(X, 𝒪_E) ⥤ D(X, ℚ̄_ℓ)` kills the objects killed by a
nonzero element `m` of `𝒪_E`: `m` acts invertibly on `K ⊗_{𝒪_E} ℚ̄_ℓ`, and by zero. -/
lemma DerivedCategoryConstructibleIntegral.isZero_extendScalarsQlbar_obj_of_torsion
    (K : DerivedCategoryConstructibleIntegral X l E)
    (hK : Rationalization.torsion (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryConstructibleIntegral X l E) K) :
    IsZero ((DerivedCategoryConstructibleIntegral.extendScalarsQlbar X l E).obj K) :=
  sorry

/-- The morphisms of `D_cons(X, 𝒪_E)` inverted in `D_cons(X, E)` are sent to isomorphisms of
`D(X, ℚ̄_ℓ)` by the extension of scalars: their mapping cones are torsion, hence are sent to
zero, as the extension of scalars is triangulated. -/
lemma DerivedCategoryConstructibleRational.isInvertedBy_extendScalarsQlbar :
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryConstructibleIntegral X l E)).IsInvertedBy
      (DerivedCategoryConstructibleIntegral.extendScalarsQlbar X l E) :=
  fun _ _ _ ⟨_, _, _, hT, hZ⟩ ↦ (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    ((DerivedCategoryConstructibleIntegral.extendScalarsQlbar X l E).map_distinguished _ hT)).1
      (DerivedCategoryConstructibleIntegral.isZero_extendScalarsQlbar_obj_of_torsion
        X l E _ hZ)

/-- The extension of scalars `- ⊗_E ℚ̄_ℓ : D_cons(X, E) ⥤ D(X, ℚ̄_ℓ)`: the functor induced by
`DerivedCategoryConstructibleIntegral.extendScalarsQlbar`, through the universal property of
the localization `D_cons(X, 𝒪_E) ⥤ D_cons(X, E)`. -/
noncomputable def DerivedCategoryConstructibleRational.extendScalarsQlbar :
    DerivedCategoryConstructibleRational X l E ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl l)))) :=
  Localization.lift (DerivedCategoryConstructibleIntegral.extendScalarsQlbar X l E)
    (DerivedCategoryConstructibleRational.isInvertedBy_extendScalarsQlbar X l E)
    (DerivedCategoryConstructibleRational.fromIntegral X l E)

/-- The extension of scalars on `D_cons(X, E)` is compatible with the one on
`D_cons(X, 𝒪_E)` through the localization functor. -/
noncomputable def DerivedCategoryConstructibleRational.fromIntegralCompExtendScalarsQlbarIso :
    DerivedCategoryConstructibleRational.fromIntegral X l E ⋙
        DerivedCategoryConstructibleRational.extendScalarsQlbar X l E ≅
      DerivedCategoryConstructibleIntegral.extendScalarsQlbar X l E :=
  Localization.fac _ _ _

end Qlbar

section Comp

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  (F : Type w') [Field F] [Algebra F (PadicAlgCl l)] [Algebra E F]
  [IsScalarTower E F (PadicAlgCl l)]
  (G : Type w'') [Field G] [Algebra G (PadicAlgCl l)] [Algebra F G] [Algebra E G]
  [IsScalarTower F G (PadicAlgCl l)] [IsScalarTower E G (PadicAlgCl l)] [IsScalarTower E F G]

/-- The inclusions of rings of integers compose along a tower `E → F → G`. -/
lemma integersMap_comp :
    (integersMap l F G).comp (integersMap l E F) = integersMap l E G :=
  RingHom.ext fun x ↦ Subtype.ext (IsScalarTower.algebraMap_apply E F G x).symm

/-- The inclusion `𝒪_E → ℚ̄_ℓ` factors through `𝒪_F`. -/
lemma algebraMap_integers_comp_integersMap :
    (algebraMap (integers l F) (PadicAlgCl l)).comp (integersMap l E F) =
      algebraMap (integers l E) (PadicAlgCl l) :=
  RingHom.ext fun x ↦ (IsScalarTower.algebraMap_apply E F (PadicAlgCl l) x).symm

variable [Small.{u + 1} E] [Small.{u + 1} F] [Small.{u + 1} G]

attribute [local instance] algebraShrinkIntegers

/-- The universe `u + 1` copies of the rings of integers of a tower `E → F → G` form a
scalar tower. -/
lemma isScalarTower_shrinkIntegers :
    IsScalarTower (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l F))
      (Shrink.{u + 1} (integers l G)) :=
  .of_algebraMap_eq fun x ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    rw [← integersMap_comp l E F G, RingHom.comp_apply]

/-- The universe `u + 1` copies of `𝒪_E`, `𝒪_F` and `ℚ̄_ℓ` form a scalar tower. -/
lemma isScalarTower_shrinkIntegers_shrink :
    IsScalarTower (Shrink.{u + 1} (integers l E)) (Shrink.{u + 1} (integers l F))
      (Shrink.{u + 1} (PadicAlgCl l)) :=
  .of_algebraMap_eq fun x ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    rw [← algebraMap_integers_comp_integersMap l E F, RingHom.comp_apply]

end PadicAlgCl

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Small.{u + 1} E]
  (F : Type w') [Field F] [Algebra F (PadicAlgCl l)] [Small.{u + 1} F] [Algebra E F]
  [IsScalarTower E F (PadicAlgCl l)]
  (G : Type w'') [Field G] [Algebra G (PadicAlgCl l)] [Small.{u + 1} G] [Algebra F G]
  [Algebra E G] [IsScalarTower F G (PadicAlgCl l)] [IsScalarTower E G (PadicAlgCl l)]
  [IsScalarTower E F G]

attribute [local instance] PadicAlgCl.algebraShrinkIntegers

/-- The extension of scalars between rings of integers is compatible with composition along
a tower `E → F → G`: `- ⊗_{𝒪_E} 𝒪_G ≅ (- ⊗_{𝒪_E} 𝒪_F) ⊗_{𝒪_F} 𝒪_G`, induced by
`Sheaf.algebraExtendScalarsComp`. -/
noncomputable def DerivedCategory.integralExtendScalarsComp :
    integralExtendScalars X l E G ≅ integralExtendScalars X l E F ⋙ integralExtendScalars X l F G :=
  letI := PadicAlgCl.isScalarTower_shrinkIntegers l E F G
  Functor.mapDerivedCategoryNatIso (Sheaf.algebraExtendScalarsComp _ _ _ _) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The extension of scalars to `ℚ̄_ℓ` is compatible with the extension of scalars between
rings of integers: `- ⊗_{𝒪_E} ℚ̄_ℓ ≅ (- ⊗_{𝒪_E} 𝒪_F) ⊗_{𝒪_F} ℚ̄_ℓ`, induced by
`Sheaf.algebraExtendScalarsComp`. -/
noncomputable def DerivedCategory.integralExtendScalarsQlbarComp :
    integralExtendScalarsQlbar X l E ≅
      integralExtendScalars X l E F ⋙ integralExtendScalarsQlbar X l F :=
  letI := PadicAlgCl.isScalarTower_shrinkIntegers_shrink l E F
  Functor.mapDerivedCategoryNatIso (Sheaf.algebraExtendScalarsComp _ _ _ _) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

section Constructible

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] F] [IsScalarTower ℚ_[l] F (PadicAlgCl l)] [FiniteDimensional ℚ_[l] F]
  [FiniteDimensional E F] [FiniteDimensional F G] [FiniteDimensional E G]

/-- The extension of scalars `D_cons(X, 𝒪_E) ⥤ D_cons(X, 𝒪_G)` is the composite of those
along `E → F` and `F → G`: `DerivedCategory.integralExtendScalarsComp`, lifted along the
fully faithful inclusion of `D_cons(X, 𝒪_G)`. -/
noncomputable def DerivedCategoryConstructibleIntegral.extendScalarsComp :
    extendScalars X l E G ≅ extendScalars X l E F ⋙ extendScalars X l F G :=
  ((DerivedCategory.constructibleIntegral X l G).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ι X l E) (DerivedCategory.integralExtendScalarsComp X l E F G))

/-- The extension of scalars `D_cons(X, 𝒪_E) ⥤ D(X, ℚ̄_ℓ)` factors through
`D_cons(X, 𝒪_F)`: this is `DerivedCategory.integralExtendScalarsQlbarComp` restricted to
`D_cons(X, 𝒪_E)`. -/
noncomputable def DerivedCategoryConstructibleIntegral.extendScalarsQlbarComp :
    extendScalarsQlbar X l E ≅ extendScalars X l E F ⋙ extendScalarsQlbar X l F :=
  Functor.isoWhiskerLeft (ι X l E) (DerivedCategory.integralExtendScalarsQlbarComp X l E F)

/-- The extension of scalars `D_cons(X, E) ⥤ D_cons(X, G)` is the composite of those along
`E → F` and `F → G`: after precomposition with the localization functor
`D_cons(X, 𝒪_E) ⥤ D_cons(X, E)`, both sides are identified with
`DerivedCategoryConstructibleIntegral.extendScalarsComp` followed by the localization functor
of `D_cons(X, 𝒪_G)`, and precomposition with a localization functor is fully faithful. -/
noncomputable def DerivedCategoryConstructibleRational.extendScalarsComp :
    extendScalars X l E G ≅ extendScalars X l E F ⋙ extendScalars X l F G :=
  (Localization.whiskeringLeftFunctor' (fromIntegral X l E) (Rationalization.W
    (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryConstructibleIntegral X l E)) _).preimageIso
    (fromIntegralCompExtendScalarsIso X l E G ≪≫
      Functor.isoWhiskerRight (DerivedCategoryConstructibleIntegral.extendScalarsComp X l E F G)
        (fromIntegral X l G) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (DerivedCategoryConstructibleIntegral.extendScalars X l E F)
        (fromIntegralCompExtendScalarsIso X l F G).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (fromIntegralCompExtendScalarsIso X l E F).symm
        (extendScalars X l F G) ≪≫
      Functor.associator _ _ _)

/-- The extension of scalars `D_cons(X, E) ⥤ D(X, ℚ̄_ℓ)` factors through `D_cons(X, F)`:
after precomposition with the localization functor `D_cons(X, 𝒪_E) ⥤ D_cons(X, E)`, both
sides are identified with `DerivedCategoryConstructibleIntegral.extendScalarsQlbarComp`, and
precomposition with a localization functor is fully faithful. -/
noncomputable def DerivedCategoryConstructibleRational.extendScalarsQlbarComp :
    extendScalarsQlbar X l E ≅ extendScalars X l E F ⋙ extendScalarsQlbar X l F :=
  (Localization.whiskeringLeftFunctor' (fromIntegral X l E) (Rationalization.W
    (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryConstructibleIntegral X l E)) _).preimageIso
    (fromIntegralCompExtendScalarsQlbarIso X l E ≪≫
      DerivedCategoryConstructibleIntegral.extendScalarsQlbarComp X l E F ≪≫
      Functor.isoWhiskerLeft (DerivedCategoryConstructibleIntegral.extendScalars X l E F)
        (fromIntegralCompExtendScalarsQlbarIso X l F).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (fromIntegralCompExtendScalarsIso X l E F).symm
        (extendScalarsQlbar X l F) ≪≫
      Functor.associator _ _ _)

end Constructible

end Comp
