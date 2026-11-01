/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData

/-! # Ordinary and derived normalization predicates for reduction and pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

CondensedRing.upperStar (spIntegralCondensed l E) f ⋙
      ordinaryReduction l E s X ≅
    ordinaryReduction l E s Y ⋙ (s.operations.geometry f).pull

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

/-- The ordinary comparison type, before localizing complexes.
Source: blueprint direct-image proof (2)--(3).
(blueprint: def-sp-integral-tower-pullback-normalizations). -/
abbrev OrdinaryPullComparison (s : Presentation l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=

/-- The derived comparison type on the ordinary unbounded localizations.
Source: blueprint direct-image proof (2)--(3).
(blueprint: def-sp-integral-tower-pullback-normalizations). -/
abbrev DerivedPullComparison (s : Presentation l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    pull l E f ⋙ derivedReduction l E s X ≅
    derivedReduction l E s Y ⋙ SpTowerShriek.pull l E s.base (s.operations.geometry f)

/-- The fixed computing-counit equation on flat-term K-flat representatives.
Source: blueprint direct-image proof (2)--(3).
(blueprint: def-sp-integral-tower-pullback-normalizations). -/
def DerivedPullNormalized (s : Presentation l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ordinary : OrdinaryPullComparison l E s f)
    (derived : DerivedPullComparison l E s f) : Prop :=
  ∀ P : CochainComplex (Modules l E Y) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E Y)
      (((spIntegralModuleEquivalence l E Y).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ i : ℤ, IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology Y) (R := spIntegralSectionRing l E Y)
      ((spIntegralModuleEquivalence l E Y).functor.obj (P.X i))) →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (SpTowerShriek.pull l E s.base (s.operations.geometry f)).map
        (reductionComplexComparison l E s Y P) ≫
      (s.operations.geometry f).pull.mapDerivedCategoryFactors.hom.app
        (((ordinaryReduction l E s Y).mapHomologicalComplex (.up ℤ)).obj P) =
    (derivedReduction l E s X).map ((pullComplexComparison l E f P).hom) ≫
      reductionComplexComparison l E s X
        (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
