/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.AlgebraicGeometry.StrictTowerOperations

/-!
# Coefficient parameters and normalization formulas for locally closed extension

The normalization predicates name the relevant equations over abstract categories,
so that their specializations can be compared without unfolding sheaf functors.

## References

* [Stacks, Tag 01OV](https://stacks.math.columbia.edu/tag/01OV)
* [Stacks, Tag 01IO](https://stacks.math.columbia.edu/tag/01IO)
* [Stacks, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A Noetherian scheme with an arbitrary commutative coefficient sheaf.
(Stacks, Tags 01OV, 09A5) -/
structure LocallyClosedCoefficients where
  scheme : Scheme.{u}
  locallyNoetherian : IsLocallyNoetherian scheme
  compact : CompactSpace scheme
  ring : Sheaf (ProEt.topology scheme) CommRingCat.{u + 1}

attribute [instance] LocallyClosedCoefficients.locallyNoetherian
  LocallyClosedCoefficients.compact

/-- A locally closed immersion with its inverse-image coefficient identification.
(Stacks, Tags 01IO, 03D2) -/
structure LocallyClosedCoefficientImmersion (S X : LocallyClosedCoefficients.{u}) where
  hom : S.scheme ⟶ X.scheme
  immersion : IsImmersion hom
  coefficient : (proEtaleSheafInverseImage hom CommRingCat.{u + 1}).obj X.ring ≅ S.ring

attribute [instance] LocallyClosedCoefficientImmersion.immersion

namespace LocallyClosedCoefficientImmersion

/-- The identity immersion, with the identity inverse-image comparison. (Stacks, Tag 09A5) -/
def identity (X : LocallyClosedCoefficients.{u}) : LocallyClosedCoefficientImmersion X X where
  hom := 𝟙 X.scheme
  immersion := inferInstance
  coefficient := (proEtaleRingInverseImageId X.scheme).app X.ring

/-- Composition of immersions, with the composed inverse-image coefficient identifications.
(Stacks, Tags 02V0, 03D8) -/
def comp {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    LocallyClosedCoefficientImmersion T X where
  hom := b.hom ≫ a.hom
  immersion := inferInstance
  coefficient := proEtaleRingCompositeCoefficients b.hom a.hom X.ring S.ring T.ring
    a.coefficient b.coefficient

/-- Exact inverse image with the specified inverse-image coefficients. (Stacks, Tag 03D2) -/
abbrev pull {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModulePullback a.hom X.ring S.ring a.coefficient

/-- Direct image with action through the coefficient adjunction unit. (Stacks, Tag 03D3) -/
abbrev push {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModuleDirectImage a.hom X.ring S.ring a.coefficient

end LocallyClosedCoefficientImmersion

/-- The specified open unit is inverse to restriction. (Stacks, Tags 03DI, 09BN) -/
def LocallyClosedOpenNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (adj : F ⊣ L) : Prop :=
  ∀ M, dsimp% only [Functor.comp_obj, Functor.id_obj]
    adj.unit.app M ≫ r.hom.app M = 𝟙 M

/-- Restriction agrees with the specified closed counit after comparison. (Stacks, Tag 09AA) -/
def LocallyClosedClosedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C) (e : F ≅ P) : Prop :=
  ∀ M, dsimp% only [Functor.comp_obj, Functor.id_obj]
    r.hom.app M = L.map (e.hom.app M) ≫ d.app M

end AlgebraicGeometry.Scheme
