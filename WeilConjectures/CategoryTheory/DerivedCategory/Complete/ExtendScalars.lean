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

## Main definitions

- `PadicAlgCl.integersMap` : the inclusion `𝒪_E → 𝒪_F` of rings of integers.
- `PadicAlgCl.algebraShrinkIntegers` : the induced algebra structure between the universe
  `u + 1` copies `Shrink 𝒪_E` and `Shrink 𝒪_F`, a local instance in this file.
- `DerivedCategory.integralExtendScalars` : the functor `D(X, 𝒪_E) ⥤ D(X, 𝒪_F)`.
- `DerivedCategoryConstructibleIntegral.extendScalars` : its restriction
  `D_cons(X, 𝒪_E) ⥤ D_cons(X, 𝒪_F)` for `F` finite over `E`.
- `DerivedCategoryConstructibleRational.extendScalars` : the induced functor
  `D_cons(X, E) ⥤ D_cons(X, F)` on the rationalizations, for `F` finite over `E`.

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
-/

@[expose] public section

universe w w' u

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

/-- The extension of scalars of sheaves of modules along the flat `Shrink 𝒪_E → Shrink 𝒪_F`
is left exact: it is sectionwise left exact by flatness, and sheafification is exact. -/
instance Sheaf.preservesFiniteLimits_algebraExtendScalars_shrinkIntegers :
    PreservesFiniteLimits (Sheaf.algebraExtendScalars (Scheme.ProEt.topology X)
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) (Shrink.{u + 1} (PadicAlgCl.integers l F))) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat.{u + 1}
    (PadicAlgCl.flat_algebraMap_shrinkIntegers l E F)
  have : PreservesFiniteLimits (ModuleCat.algebraExtendScalars.{u + 1}
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) (Shrink.{u + 1} (PadicAlgCl.integers l F))) :=
    preservesFiniteLimits_of_natIso (Adjunction.leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj.{u + 1} _)
      (ModuleCat.algebraExtendRestrictScalarsAdj _ _))
  have : PreservesFiniteLimits ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
      (ModuleCat.algebraExtendScalars.{u + 1}
        (Shrink.{u + 1} (PadicAlgCl.integers l E)) (Shrink.{u + 1} (PadicAlgCl.integers l F)))) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  dsimp only [Sheaf.algebraExtendScalars, Sheaf.composeAndSheafify]
  infer_instance

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
