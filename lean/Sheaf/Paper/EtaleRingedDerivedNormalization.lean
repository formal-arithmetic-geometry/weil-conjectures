module

public import Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData
public import Sheaf.CategoryTheory.DerivedProjectionComparisonSquares

public import Sheaf.Paper.EtaleRingedProjectionPresentation
public import Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData
public import Sheaf.Paper.RingedProjectionTensorAssociativity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Étale and ringed-site projection identifications

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: def-pur-etale-ringed-derived-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w a h

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open CategoryTheory.ConstantScalarRestriction CategoryTheory.ConstantModuleDerivedProjection

namespace AlgebraicGeometry.Etale.RingedProjectionIdentification

/-- Localization of the canonical ordinary scalar-extension comparison on every complex.
Source: Stacks 07A4 and 07A6
(blueprint: def-pur-etale-ringed-derived-normalization). -/
def NativeLeftNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology Y) Λ)]
    [HasDerivedCategory.{u + 1} (Modules (topology X) Λ)]
    (d : GeometricData (topology Y) (topology X) Λ) (x : ExactData d)
    (o : OrdinaryIdentification d)
    (hL : d.pullA = transportedInverse f (ModuleCat.{u + 1} Λ))
    (i : d.pullR.mapDerivedCategory ⋙ derivedToNative X Λ ≅
      derivedToNative Y Λ ⋙ (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor) : Prop :=
  ∀ P : CochainComplex (Modules (topology Y) Λ) ℤ,
    i.hom.app (DerivedCategory.Q.obj P) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).hom.app
          ((derivedToNative Y Λ).obj (DerivedCategory.Q.obj P)) ≫
        (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.map
          ((toNative Y Λ).mapDerivedCategoryFactors.hom.app P) ≫
        (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryFactors.hom.app
          (((toNative Y Λ).mapHomologicalComplex (.up ℤ)).obj P) =
      (derivedToNative X Λ).map (d.pullR.mapDerivedCategoryFactors.hom.app P) ≫
        (toNative X Λ).mapDerivedCategoryFactors.hom.app
          ((d.pullR.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryNativeLeft f Λ d o hL) (.up ℤ)).hom.app P)

/-- The right-derived comparison commutes with the universal comparison on every complex;
on K-injectives it is the ordinary direct-image comparison.
Source: Stacks 07A6
(blueprint: def-pur-etale-ringed-derived-normalization). -/
def NativeRightNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology Y) Λ)]
    [HasDerivedCategory.{u + 1} (Modules (topology X) Λ)]
    (d : GeometricData (topology Y) (topology X) Λ) (_x : ExactData d)
    (o : OrdinaryIdentification d)
    (hR : d.pushA = transportedDirect f (ModuleCat.{u + 1} Λ))
    (j : d.pushR.rightDerivedFunctor ⋙ derivedToNative Y Λ ≅
      derivedToNative X Λ ⋙ (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor) : Prop :=
  ∀ P : CochainComplex (Modules (topology X) Λ) ℤ,
    (derivedToNative Y Λ).map
        (d.pushR.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
        j.hom.app (DerivedCategory.Q.obj P) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
          ((toNative X Λ).mapDerivedCategoryFactors.hom.app P) =
      (toNative Y Λ).mapDerivedCategoryFactors.hom.app
        ((d.pushR.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ordinaryNativeRight f Λ d o hR) (.up ℤ)).hom.app P) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj
          (((toNative X Λ).mapHomologicalComplex (.up ℤ)).obj P))

/-- The normalized ringed monoidal pullback. Its ordinary comparison is the specified
scalar-extension pure-tensor comparison, and its derived comparison is its signed total.
Source: Stacks 03EL and 07A4
(blueprint: def-pur-etale-ringed-derived-normalization). -/
def RingedPullbackTensorData {X Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology Y) Λ)]
    [HasDerivedCategory.{u + 1} (Modules (topology X) Λ)]
    (d : GeometricData (topology Y) (topology X) Λ) (x : ExactData d) :=
  { m : d.pullR.mapDerivedCategory.Monoidal × d.pullR.Monoidal //
    (∀ M N : Modules (topology Y) Λ,
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ d.pullR m.2.toOplaxMonoidal M N =
        (d.ringTensor.mu M N).hom) ∧
    TensorNormalization (Modules (topology Y) Λ) (Modules (topology X) Λ)
      d.pullR m.2 m.1 }


end AlgebraicGeometry.Etale.RingedProjectionIdentification
