/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealization
public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerFiniteSiteComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralExceptionalInverseImage

/-! # Canonical compact-support comparison in strict quotient coordinates

Source: current blueprint sk-prop-sp-integral-adjunction, outer Hom comparisons;
Zheng Constructions 4.1 and 5.15, Lemma 4.10; the universal-unit normalization of
integralExceptionalComparison_characterization
(blueprint: def-pur-integral-support-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules Opposite
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
attribute [local instance] BrownTowerComparison.ProCompact.openAdditive
namespace WeilConjectures.PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing sectionwise quotient-coordinate equivalence on ordinary derived systems.
Only the standard localization instance is chosen to match the Brown interface.
Source: blueprint integral Hom display; integralExceptionalCoordinates
(blueprint: def-pur-integral-support-comparison-data). -/
def coordinates (W : Scheme.{u}) :
    coefficientSequenceDerived.{u, u} l E W ≌
      DerivedCategory (BrownTowerComparison.ProSystem W
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)) :=
  haveI := Functor.isEquivalence_mapDerivedCategory (integralExceptionalCoordinates l E W)
  (integralExceptionalCoordinates l E W).mapDerivedCategory.asEquivalence

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

open CompactSupportCondensedRealization
open AlgebraicGeometry.ProEtale
attribute [local instance 6000] SemilinearProperOpen.extension_additive
  SemilinearProperOpen.push_additive integralExceptionalCoordinates_additive
attribute [local irreducible] SemilinearProperOpen.push

/-- Ordinary direct-image coordinates are fixed by the identity on every underlying
section after the dependency's rightEvaluation and rightUnderlying comparisons.
Source: Zheng 4.1, 4.10; integralExceptionalComparison_characterization
(blueprint: def-pur-integral-support-comparison-data). -/
def PushNormalized {T U : Scheme.{u}} (g : T ⟶ U)
    (B : CoefficientSystemOrdinaryImage
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology T)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1))))
    (a : SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) g ⋙
        integralExceptionalCoordinates l E U ≅
      integralExceptionalCoordinates l E T ⋙ B.rightSystem) : Prop :=
  ∀ (M : coefficientSequenceModules l E T) (n : ℕ) (V : U.ProEtᵒᵖ)
    (x : (((SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) g ⋙
      integralExceptionalCoordinates l E U).obj M).level n).val.obj V),
    HEq (((B.rightUnderlying n).hom.app
        (((integralExceptionalCoordinates l E T).obj M).level n)).hom.app V
      (((B.rightEvaluation n).hom.app ((integralExceptionalCoordinates l E T).obj M)).val.app V
        (((a.hom.app M).app n).val.app V x))) x

/-- All comparisons, with their normalization equations. The ordinary push maps are
identity on sections; the inverse and extension maps are their adjunction transposes;
the derived open map is fixed on complexes; the proper map is fixed by its universal
right-derived unit. Thus no automorphism twist of the final beta is admitted.
Source: blueprint outer Hom comparisons; Zheng 4.1, 4.10, 5.15
(blueprint: def-pur-integral-support-comparison-data). -/
structure Ordinary where
  openPush : SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) c.i ⋙
      integralExceptionalCoordinates l E c.Z ≅
    integralExceptionalCoordinates l E X ⋙ D.compact.openImage.rightSystem
  openPush_normalized : PushNormalized l E c.i D.compact.openImage openPush
  properPush : SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) c.g ⋙
      integralExceptionalCoordinates l E Y ≅
    integralExceptionalCoordinates l E c.Z ⋙ D.compact.properImage.rightSystem
  properPush_normalized : PushNormalized l E c.g D.compact.properImage properPush
  openPull : integralExceptionalCoordinates l E c.Z ⋙ D.compact.openImage.inverse ≅
    SemilinearProperOpen.pull (quotientRings l E) (quotientMaps l E) c.i ⋙
      integralExceptionalCoordinates l E X
  openPull_transpose : ∀ (M : coefficientSequenceModules l E c.Z)
    (N : coefficientSequenceModules l E X)
    (h : (SemilinearProperOpen.pull (quotientRings l E) (quotientMaps l E) c.i).obj M ⟶ N),
    D.compact.openImage.systemAdj.homEquiv _ _
        (openPull.hom.app M ≫ (integralExceptionalCoordinates l E X).map h) =
      (integralExceptionalCoordinates l E c.Z).map
        ((SemilinearProperOpen.ordinaryAdj (quotientRings l E) (quotientMaps l E)
          c.i).homEquiv M N h) ≫ openPush.hom.app N
  openExtension : integralExceptionalCoordinates l E X ⋙ D.compact.openExtension ≅
    SemilinearProperOpen.extension (quotientRings l E) (quotientMaps l E) c.i ⋙
      integralExceptionalCoordinates l E c.Z
  openExtension_transpose : ∀ (M : coefficientSequenceModules l E X)
    (N : coefficientSequenceModules l E c.Z)
    (h : (SemilinearProperOpen.extension (quotientRings l E) (quotientMaps l E) c.i).obj M ⟶ N),
    D.compact.openAdjunction.homEquiv _ _
        (openExtension.hom.app M ≫ (integralExceptionalCoordinates l E c.Z).map h) ≫
        openPull.hom.app N =
      (integralExceptionalCoordinates l E X).map
        ((SemilinearProperOpen.ordinaryOpenAdj (quotientRings l E) (quotientMaps l E)
          c.i).homEquiv M N h)

/-- Representative and universal-unit equations over the fixed ordinary comparisons.
Source: Stacks 05RU, 0D6E; blueprint integral Hom display
(blueprint: def-pur-integral-support-comparison-data). -/
structure Derived (B : Ordinary l E S G H D) where
  openComplex :
    letI := SemilinearProperOpen.extension_additive (quotientRings l E) (quotientMaps l E) c.i
    ∀ P : CochainComplex (coefficientSequenceModules l E X) ℤ,
    (D.compact.openExtension.mapHomologicalComplex (.up ℤ)).obj
        (((integralExceptionalCoordinates l E X).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((integralExceptionalCoordinates l E c.Z).mapHomologicalComplex (.up ℤ)).obj
        (((SemilinearProperOpen.extension (quotientRings l E) (quotientMaps l E)
            c.i).mapHomologicalComplex (.up ℤ)).obj P)
  openComplex_component : ∀ P (i : ℤ), (openComplex P).f i =
    B.openExtension.hom.app (P.X i)
  properComplex :
    letI := SemilinearProperOpen.push_additive (quotientRings l E) (quotientMaps l E) c.g
    ∀ P : CochainComplex (coefficientSequenceModules l E c.Z) ℤ,
    (D.compact.properImage.rightSystem.mapHomologicalComplex (.up ℤ)).obj
        (((integralExceptionalCoordinates l E c.Z).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((integralExceptionalCoordinates l E Y).mapHomologicalComplex (.up ℤ)).obj
        (((SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E)
            c.g).mapHomologicalComplex (.up ℤ)).obj P)
  properComplex_component : ∀ P (i : ℤ), (properComplex P).f i =
    B.properPush.inv.app (P.X i)
  derivedOpen : (coordinates l E X).functor ⋙ D.compact.derivedOpen ≅
    SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) c.i ⋙
      (coordinates l E c.Z).functor
  derivedOpen_factors :
    letI := SemilinearProperOpen.extension_additive (quotientRings l E) (quotientMaps l E) c.i
    ∀ P : CochainComplex (coefficientSequenceModules l E X) ℤ,
    derivedOpen.hom.app (DerivedCategory.Q.obj P) ≫
        (coordinates l E c.Z).functor.map
          ((SemilinearProperOpen.extension (quotientRings l E) (quotientMaps l E)
            c.i).mapDerivedCategoryFactors.hom.app P) ≫
        (integralExceptionalCoordinates l E c.Z).mapDerivedCategoryFactors.hom.app
          (((SemilinearProperOpen.extension (quotientRings l E) (quotientMaps l E)
            c.i).mapHomologicalComplex (.up ℤ)).obj P) =
      D.compact.derivedOpen.map
          ((integralExceptionalCoordinates l E X).mapDerivedCategoryFactors.hom.app P) ≫
        D.compact.openFactors.hom.app
          (((integralExceptionalCoordinates l E X).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (DerivedCategory.Q (C := BrownTowerComparison.ProSystem c.Z
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E))).map
        (openComplex P)
  derivedProper : (coordinates l E c.Z).functor ⋙ D.compact.properDerived.direct ≅
    SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) c.g ⋙
      (coordinates l E Y).functor
  derivedProper_unit :
    letI := SemilinearProperOpen.push_additive (quotientRings l E) (quotientMaps l E) c.g
    ∀ P : CochainComplex (coefficientSequenceModules l E c.Z) ℤ,
    D.compact.properDerived.directUnit.app
        (((integralExceptionalCoordinates l E c.Z).mapHomologicalComplex (.up ℤ)).obj P) ≫
        D.compact.properDerived.direct.map
          ((integralExceptionalCoordinates l E c.Z).mapDerivedCategoryFactors.inv.app P) ≫
        derivedProper.hom.app (DerivedCategory.Q.obj P) =
      (DerivedCategory.Q (C := BrownTowerComparison.ProSystem Y
          (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E))).map
        (properComplex P) ≫
        (integralExceptionalCoordinates l E Y).mapDerivedCategoryFactors.inv.app
          (((SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E)
            c.g).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (coordinates l E Y).functor.map
          (rightUnitApp
            (SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) c.g) P)

/-- The ordinary and derived normalization data together; splitting the records
keeps elaboration of the specified representative maps local.
Source: blueprint integral Hom display
(blueprint: def-pur-integral-support-comparison-data). -/
structure Normalized where
  ordinary : Ordinary l E S G H D
  derived : Derived l E S G H D ordinary

end WeilConjectures.PurIntegralSupportComparison
