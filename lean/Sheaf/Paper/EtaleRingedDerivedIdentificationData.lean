module

public import Sheaf.CategoryTheory.DerivedProjectionComparisonSquares

public import Sheaf.Paper.EtaleRingedDerivedNormalization
public import Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData
public import Sheaf.Paper.RingedProjectionTensorAssociativity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Étale and ringed-site projection identifications

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: def-pur-etale-ringed-derived-identification-data).
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

/-- The scalar comparison with the published native etale functors. The comparison
contains the Hom bijection, unit, counit, tensor square and projection mate square.
Source: Stacks 07A4, 07A6 and 0B56
(blueprint: def-pur-etale-ringed-derived-identification-data). -/
def NativeIdentification {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology Y) Λ)]
    [HasDerivedCategory.{u + 1} (Modules (topology X) Λ)]
    (d : GeometricData (topology Y) (topology X) Λ) (x : ExactData d)
    (o : OrdinaryIdentification d)
    (hL : d.pullA = transportedInverse f (ModuleCat.{u + 1} Λ))
    (hR : d.pushA = transportedDirect f (ModuleCat.{u + 1} Λ))
    (mY : NativeOrdinaryTensorData Y Λ) (mX : NativeOrdinaryTensorData X Λ)
    (cY : NativeTensorData Y Λ mY.braided) (cX : NativeTensorData X Λ mX.braided) :=
  NormalizedComparison
    d.pullR.mapDerivedCategory d.pushR.rightDerivedFunctor
    (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor
    d.ringAdj.mapDerivedCategoryRightDerivedAdjunction
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (derivedToNative Y Λ) (derivedToNative X Λ) cY.val cX.val
    (NativeLeftNormalization f Λ d x o hL) (NativeRightNormalization f Λ d x o hR)
    (fun _ ↦ RingedPullbackTensorData Λ d x)
    (fun _ t ↦ t.val.1)
    (fun _ _ ↦ leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) f)

/-- The canonical projection square written using the two published projection maps.
Every input is an arbitrary object of the unbounded derived category.
Source: Stacks 0B56, equation-projection-formula-map
(blueprint: def-pur-etale-ringed-derived-identification-data). -/
def PublishedProjectionSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology Y) Λ)]
    [HasDerivedCategory.{u + 1} (Modules (topology X) Λ)]
    (d : GeometricData (topology Y) (topology X) Λ) (x : ExactData d)
    (o : OrdinaryIdentification d)
    (hL : d.pullA = transportedInverse f (ModuleCat.{u + 1} Λ))
    (hR : d.pushA = transportedDirect f (ModuleCat.{u + 1} Λ))
    (mY : NativeOrdinaryTensorData Y Λ) (mX : NativeOrdinaryTensorData X Λ)
    (cY : NativeTensorData Y Λ mY.braided) (cX : NativeTensorData X Λ mX.braided)
    (e : NativeIdentification f Λ d x o hL hR mY mX cY cX)
    (a : SheafOfModules.RingedTensorModel (corner Y Λ))
    (b : SheafOfModules.RingedTensorModel (corner X Λ)) : Prop :=
  letI := cY.val
  letI := cX.val
  ∀ (E : DerivedCategory (Modules (topology X) Λ))
    (L : DerivedCategory (Modules (topology Y) Λ)),
    (derivedToNative Y Λ).map ((edge Λ d x).projection a b E L) ≫
      e.right.hom.app (E ⊗ d.pullR.mapDerivedCategory.obj L) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
        (Functor.OplaxMonoidal.δ (derivedToNative X Λ) E
          (d.pullR.mapDerivedCategory.obj L) ≫ (𝟙 _ ⊗ₘ e.left.hom.app L)) =
    Functor.OplaxMonoidal.δ (derivedToNative Y Λ) (d.pushR.rightDerivedFunctor.obj E) L ≫
      (e.right.hom.app E ⊗ₘ 𝟙 _) ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app
        ((derivedToNative X Λ).obj E)).app ((derivedToNative Y Λ).obj L)


end AlgebraicGeometry.Etale.RingedProjectionIdentification
