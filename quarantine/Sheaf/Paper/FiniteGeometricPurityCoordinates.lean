/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.Paper.FiniteReductionRootCharts
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AmbientAdjointClass
public import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Sheaf.Paper.FiniteRootLinePowerTransition
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Sheaf.Paper.FiniteCoefficientSmoothPurity
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-!
# Finite geometric Frobenius and the counit mate of smooth purity

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Steps 1--2;
sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.md.
(blueprint: def-pur-finite-geometric-purity-coordinates).

All maps are in the existing fixed-scalar presentation of the small pro-etale
category. The realization unit conjugates the already recorded smoothPurityMap.
The compact-support map is the proper/open exchange followed by the canonical
compactification comparison on etale-origin inputs. Its mate is determined by the
counit equation, rather than by a choice of an endpoint isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Exact inverse image has its termwise shift comparison in the purity coordinates.
Source: blueprint equivariance, shift factor of b_K
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityPullbackCommShift (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (P.smoothPurityPullback f).CommShift ℤ :=
  inferInstanceAs
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory.CommShift ℤ)

/-- The field automorphism gamma used in the recorded scheme Frobenius.
Source: blueprint equivariance, Step 1
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityGamma (P : PurityFiniteSetting.{u}) : P.field.k ≃ₐ[P.field.k₀] P.field.k :=
  @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
    (Fintype.ofFinite P.field.k₀) _ _ _

/-- Retag the structure map and retain precisely the same underlying scheme.
Source: blueprint equivariance, retagging in Step 1
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityRetag (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (.of P.field.k₀))) : Over (Spec (.of P.field.k)) :=
  (Over.map (Spec.map (CommRingCat.ofHom P.geometricPurityGamma.toRingHom))).obj
    (P.frobeniusFiber T₀)

/-- The same finite-type-over-field compactification used by smoothPurityMap.
Source: blueprint equivariance, the unchanged compactification
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityCompactification (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    Compactification f :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI : HasCompactification f := inferInstance
  HasCompactification.compactification f

/-- Compact support in the fixed-scalar presentation, at the retained compactification.
Source: blueprint equivariance, F = Rf_!
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityF (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) (P.geometricPurityCompactification f aY)

/-- The standing exceptional counit, totalized by zero outside its bounded-below scope.
Only the bounded constructible scope occurs in the assertions below.
Source: blueprint equivariance, epsilon and its ordinary-etale normalization
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityCounit (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient))) :
    (P.geometricPurityF f aY).obj ((P.smoothPurityExceptionalOver f aY).obj M) ⟶ M := by
  classical
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  letI : HasCompactification f := inferInstance
  exact if hM : DerivedCategory.TStructure.t.plus M then
    ProEtale.rightDerivedUpperShriekCounit f M hM else 0

/-- The fixed-scalar coordinates of the canonical purity map, including both realization
units. Thus this is the existing Gamma, not a newly selected orientation or tensor map.
Source: blueprint equivariance, Gamma_K
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityMap (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj M)) :
    (P.compositionTwistShift X d).obj ((P.smoothPurityPullback f).obj M) ⟶
      (P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).obj M :=
  (P.smoothPurityPullback f ⋙ P.compositionTwistShift X d).map
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.hom.app M) ≫
    (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj M)))).hom ≫
    (P.existsUnique_smoothPurityTensorMap f d
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj M) hM).exists.choose ≫
    (P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.inv.app M)

/-- The canonical inverse-image square in exactly the fixed-scalar purity coordinates.
Source: blueprint equivariance, pullback-composition factor of b_K
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityPullbackSquare (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient))) :
    (P.smoothPurityPullback gX).obj ((P.smoothPurityPullback f).obj M) ≅
      (P.smoothPurityPullback f).obj ((P.smoothPurityPullback gY).obj M) :=
  ((compositionFixedPullbackComp P.Ring gX f).app M).symm ≪≫
    eqToIso (congrArg (fun h ↦ (P.smoothPurityPullback h).obj M) w) ≪≫
    (compositionFixedPullbackComp P.Ring f gY).app M

/-- The normalized compact-support exchange in fixed-scalar coordinates. The middle
word is literally the published proper/open base-change map. Its target is compared
back to the retained compactification on etale-origin objects. The zero branch only
extends this formula beyond the bounded class in the statement.
Source: blueprint equivariance, B_M of def-exchange-projection
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityB (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (gX : X ⟶ X) (gY : Y ⟶ Y) (sq : IsPullback gX f f gY)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient))) :
    (P.smoothPurityPullback gY).obj ((P.geometricPurityF f aY).obj M) ⟶
      (P.geometricPurityF f aY).obj ((P.smoothPurityPullback gX).obj M) := by
  classical
  let A := ModuleCat.{u + 1} P.Coefficient
  let c := P.geometricPurityCompactification f aY
  let q := (ProEtale.upperStar A gX).leftDerivedFunctor.obj M
  exact if hq : AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin A X q then
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A gY).inv.app
        ((P.geometricPurityF f aY).obj M) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c).app M ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso
        P.Coefficient (c.ofIsPullback sq) c).hom.app ⟨q, hq⟩ ≫
      (P.geometricPurityF f aY).map
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A gX).hom.app M)
    else 0

private theorem compactification_independent (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a a' : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a]
    [LocallyOfFiniteType a'] [QuasiCompact a'] :
    P.geometricPurityCompactification f a = P.geometricPurityCompactification f a' := rfl

private theorem orientation_independent (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a a' : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a]
    [LocallyOfFiniteType a'] [QuasiCompact a']
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    HEq (P.diagonalDualizingObject d f a) (P.diagonalDualizingObject d f a') := HEq.rfl

private theorem tensorPresentation_independent (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a a' : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a]
    [LocallyOfFiniteType a'] [QuasiCompact a']
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient)))
    (M₀ : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj M₀ ≅ M) :
    HEq (P.smoothPurityTensorMapInPresentation f d a M M₀ e)
      (P.smoothPurityTensorMapInPresentation f d a' M M₀ e) := HEq.rfl

private theorem counit_independent (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a a' : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a]
    [LocallyOfFiniteType a'] [QuasiCompact a']
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient))) :
    HEq (P.geometricPurityCounit f a M) (P.geometricPurityCounit f a' M) := HEq.rfl

section GeometricDomain
variable (P : PurityFiniteSetting.{u})
variable (X₀ Y₀ : Over (Spec (.of P.field.k₀)))
variable [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
variable [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
variable (f₀ : X₀ ⟶ Y₀)
variable [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]

/-- Finite type and separatedness of each geometric fiber, including the empty model.
Source: blueprint equivariance, geometry of Step 1
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: the structure map is the base change of the model structure map. Each of
locally finite type, quasi-compactness and separatedness is stable under base change. -/
theorem geometricPurityFiberProperties (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    LocallyOfFiniteType (P.frobeniusFiber T₀).hom ∧
      QuasiCompact (P.frobeniusFiber T₀).hom ∧
      IsSeparated ((P.frobeniusFiber T₀).left ↘ Spec (.of P.field.k)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.baseChange_obj _ T₀
      (inferInstance : LocallyOfFiniteType T₀.hom)
  · exact MorphismProperty.baseChange_obj _ T₀
      (inferInstance : QuasiCompact T₀.hom)
  · exact MorphismProperty.baseChange_obj _ T₀
      (inferInstance : IsSeparated T₀.hom)

set_option linter.unusedSectionVars false in
/-- The relative finite-type and separated properties are unchanged by base change.
Source: blueprint equivariance, f after geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: apply stability under base change to each property of f0.left using the
Cartesian square defining Over.pullback.map. No geometric connectedness is required. -/
theorem geometricPurityMapProperties :
    IsSeparated (P.frobeniusMap f₀) ∧ LocallyOfFiniteType (P.frobeniusMap f₀) ∧
      QuasiCompact (P.frobeniusMap f₀) := by
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.overPullbackMap _ f₀
      (inferInstance : IsSeparated f₀.left)
  · exact MorphismProperty.overPullbackMap _ f₀
      (inferInstance : LocallyOfFiniteType f₀.left)
  · exact MorphismProperty.overPullbackMap _ f₀
      (inferInstance : QuasiCompact f₀.left)

end GeometricDomain

/-- The actual geometric fibers inherit their finite-type instances.
Source: blueprint equivariance, geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityFiberLft (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    LocallyOfFiniteType ((P.frobeniusFiber T₀).left ↘ Spec (.of P.field.k)) :=
  (P.geometricPurityFiberProperties T₀).1

/-- Quasi-compactness of the actual geometric fiber.
Source: blueprint equivariance, geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityFiberQc (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    QuasiCompact ((P.frobeniusFiber T₀).left ↘ Spec (.of P.field.k)) :=
  (P.geometricPurityFiberProperties T₀).2.1

/-- Separatedness of the actual geometric fiber.
Source: blueprint equivariance, geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityFiberSeparated (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    IsSeparated ((P.frobeniusFiber T₀).left ↘ Spec (.of P.field.k)) :=
  (P.geometricPurityFiberProperties T₀).2.2

/-- The same geometric structure-map property in explicit Over coordinates.
Source: blueprint equivariance, geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityExplicitLft (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    LocallyOfFiniteType (P.frobeniusFiber T₀).hom :=
  (P.geometricPurityFiberProperties T₀).1

/-- The same geometric structure-map property in explicit Over coordinates.
Source: blueprint equivariance, geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityExplicitQc (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    QuasiCompact (P.frobeniusFiber T₀).hom :=
  (P.geometricPurityFiberProperties T₀).2.1

/-- The same geometric structure-map property in explicit Over coordinates.
Source: blueprint equivariance, geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityExplicitSeparated (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    IsSeparated (P.frobeniusFiber T₀).hom :=
  (P.geometricPurityFiberProperties T₀).2.2

/-- Relative separatedness inherited from the model.
Source: blueprint equivariance, geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityRelativeSeparated (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (.of P.field.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] :
    IsSeparated (P.frobeniusMap f₀) :=
  (P.geometricPurityMapProperties X₀ Y₀ f₀).1

/-- Relative locally finite type inherited from the model.
Source: blueprint equivariance, geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityRelativeLft (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (.of P.field.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] :
    LocallyOfFiniteType (P.frobeniusMap f₀) :=
  (P.geometricPurityMapProperties X₀ Y₀ f₀).2.1

/-- Relative quasi-compactness inherited from the model.
Source: blueprint equivariance, geometric base change
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityRelativeQc (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (.of P.field.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] :
    QuasiCompact (P.frobeniusMap f₀) :=
  (P.geometricPurityMapProperties X₀ Y₀ f₀).2.2

section FixedDomain
variable (P : PurityFiniteSetting.{u})
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable (d : ℕ) [SmoothOfRelativeDimension d f]

/-- Invertibility of the recorded Gamma in fixed-scalar coordinates.
Source: blueprint equivariance, final cancellation
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: finite-coefficient smooth purity makes smoothPurityMap invertible. The two
realization units conjugating it are isomorphisms. The realization equivalence
reflects isomorphisms, giving precisely this fixed-scalar arrow. -/
theorem geometricPurityMapIsIso
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj M)) :
    IsIso (P.geometricPurityMap f d M hM) := by
  let E := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let K := (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj M
  let t := (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).hom
  let g := (P.existsUnique_smoothPurityTensorMap f d K hM).exists.choose
  have hm := P.isIso_smoothPurityMap f d K hM
  have : IsIso (E.functor.map (t ≫ g)) := by
    simpa only [smoothPurityMap, smoothPurityTensorMap, Functor.map_comp] using hm
  have : IsIso (t ≫ g) := isIso_of_reflects_iso _ E.functor
  have : IsIso g := IsIso.of_isIso_comp_left t g
  dsimp only [geometricPurityMap]
  infer_instance

/-- The inverse used in the literal displayed purity formula is the inverse of Gamma.
Source: blueprint equivariance, (Q Gamma_K)^-1
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityIso
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj M)) :=
  letI := P.geometricPurityMapIsIso f d M hM
  asIso (P.geometricPurityMap f d M hM)

end FixedDomain

section Frobenius
variable (P : PurityFiniteSetting.{u})
variable (X₀ Y₀ : Over (Spec (.of P.field.k₀)))
variable [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
variable [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
variable (f₀ : X₀ ⟶ Y₀)
variable [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
variable (d : ℕ) [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]

/-- Retagging preserves the full separated finite-type domain, fixes the underlying
scheme and makes geometric Frobenius a k-morphism to the original fiber.
Source: blueprint equivariance, semilinear retagging
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: Spec gamma is an isomorphism. Compose the structure map with it; finite
type and separatedness are stable under composition. The second projection
identity of galoisMap says exactly g_T followed by a_T equals a_T followed by
Spec gamma, and the underlying object of Over.map is definitionally unchanged. -/
theorem geometricPurityRetagProperties (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    (P.geometricPurityRetag T₀).left = (P.frobeniusFiber T₀).left ∧
      LocallyOfFiniteType (P.geometricPurityRetag T₀).hom ∧
      QuasiCompact (P.geometricPurityRetag T₀).hom ∧
      IsSeparated (P.geometricPurityRetag T₀).hom ∧
      P.frobeniusGaloisMap T₀ ≫ (P.frobeniusFiber T₀).hom =
        (P.geometricPurityRetag T₀).hom := by
  let e := P.geometricPurityGamma.toRingEquiv.toCommRingCatIso
  have : IsIso (CommRingCat.ofHom P.geometricPurityGamma.toRingHom) := e.isIso_hom
  have : IsIso (Spec.map (CommRingCat.ofHom P.geometricPurityGamma.toRingHom)) :=
    inferInstance
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · change LocallyOfFiniteType ((P.frobeniusFiber T₀).hom ≫ _)
    infer_instance
  · change QuasiCompact ((P.frobeniusFiber T₀).hom ≫ _)
    infer_instance
  · change IsSeparated ((P.frobeniusFiber T₀).hom ≫ _)
    infer_instance
  · exact (P.field.galoisMap_projections T₀.hom P.geometricPurityGamma).2

/-- Finite type of the retagged structure map.
Source: blueprint equivariance, retagging
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityRetagLft (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    LocallyOfFiniteType (P.geometricPurityRetag T₀).hom :=
  (P.geometricPurityRetagProperties T₀).2.1

/-- Quasi-compactness of the retagged structure map.
Source: blueprint equivariance, retagging
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
instance geometricPurityRetagQc (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    QuasiCompact (P.geometricPurityRetag T₀).hom :=
  (P.geometricPurityRetagProperties T₀).2.2.1

/-- The retagged k-morphism f is the existing Over.map of its geometric base change.
Source: blueprint equivariance, f^gamma
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityRetagMap : P.geometricPurityRetag X₀ ⟶ P.geometricPurityRetag Y₀ :=
  (Over.map (Spec.map (CommRingCat.ofHom P.geometricPurityGamma.toRingHom))).map
    ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).map f₀)

/-- Geometric Frobenius as a k-morphism from the retagged scheme to the original one.
Its equality is precisely the semilinear structure-map identity.
Source: blueprint equivariance, g_T on the retagged source
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityRetagFrobenius (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    P.geometricPurityRetag T₀ ⟶ P.frobeniusFiber T₀ :=
  Over.homMk (P.frobeniusGaloisMap T₀) (P.geometricPurityRetagProperties T₀).2.2.2.2

/-- The retagged square is the Cartesian Frobenius square. The same compactification,
canonical exceptional counit, diagonal orientation and tensor purity transpose survive
retagging. The heterogeneous equalities merely allow the two structure-map parameters;
the site and coefficient categories are the identical underlying categories.
Source: blueprint equivariance, retagging and both purity factors
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: the Frobenius square is Cartesian independently of the field tag. Retagging
changes no site, complex, compactification or projection word. The unique
counit-preserving right-adjoint identification is therefore the identity in these
coordinates. Diagonal-orientation ground-field invariance identifies Pi. The
projection word and counit compute the same tensor transpose; injectivity of the
adjunction Hom bijection identifies theta and then its composite with Pi inverse.
The assertion holds in relative dimension zero as well. -/
theorem geometricPurityRetagging :
    IsPullback (P.geometricPurityRetagFrobenius X₀).left
      (P.geometricPurityRetagMap X₀ Y₀ f₀).left (P.frobeniusMap f₀)
      (P.geometricPurityRetagFrobenius Y₀).left ∧
    P.geometricPurityCompactification (P.frobeniusMap f₀)
        (P.geometricPurityRetag Y₀).hom =
      P.geometricPurityCompactification (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom ∧
    HEq (P.diagonalDualizingObject d (P.frobeniusMap f₀)
        (P.geometricPurityRetag Y₀).hom)
      (P.diagonalDualizingObject d (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom) ∧
    (∀ (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
          (ModuleCat.{u + 1} P.Coefficient)))
        (M₀ : DerivedCategory (Sheaf (P.frobeniusFiber Y₀).left.smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient)))
        (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
          (P.frobeniusFiber Y₀).left).mapDerivedCategory.obj M₀ ≅ M),
      HEq (P.smoothPurityTensorMapInPresentation (P.frobeniusMap f₀) d
          (P.geometricPurityRetag Y₀).hom M M₀ e)
        (P.smoothPurityTensorMapInPresentation (P.frobeniusMap f₀) d
          (P.frobeniusFiber Y₀).hom M M₀ e)) ∧
    (∀ M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
          (ModuleCat.{u + 1} P.Coefficient)),
      HEq (P.geometricPurityCounit (P.frobeniusMap f₀)
          (P.geometricPurityRetag Y₀).hom M)
        (P.geometricPurityCounit (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom M)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1
  · exact compactification_independent P _ _ _
  · exact orientation_independent P _ _ _ d
  · intro M M₀ e
    exact tensorPresentation_independent P _ _ _ d M M₀ e
  · intro M
    exact counit_independent P _ _ _ M

/-- Root-chart expression of b_K. The target primitive root is gamma(zeta): geometric
inverse image acts on the coefficient roots by the actual field automorphism. Hence
this is the specified roots-of-unity tau_d, including its degree-zero unit case.
Source: blueprint equivariance, canonical b_K and tau_d
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPuritySourceInChart
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :=
  (P.smoothPurityPullback (P.frobeniusGaloisMap X₀)).mapIso
      (P.finiteReductionFixedChart (P.frobeniusFiber X₀).left d ζ hζ
        ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj M)) ≪≫
    ((P.smoothPurityPullback (P.frobeniusGaloisMap X₀)).commShiftIso
      (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (P.geometricPurityPullbackSquare (P.frobeniusMap f₀)
        (P.frobeniusGaloisMap X₀) (P.frobeniusGaloisMap Y₀)
        (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1 M) ≪≫
    (P.finiteReductionFixedChart (P.frobeniusFiber X₀).left d
      (P.geometricPurityGamma ζ) (hζ.map_of_injective P.geometricPurityGamma.injective)
      ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj
        ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M))).symm

private theorem geometricPurityOrderedPower_nsmul {C : Type*} [Category C] [Preadditive C]
    (T : C ⥤ C ⥤ C) [∀ M : C, (T.obj M).Additive]
    [∀ M : C, (T.flip.obj M).Additive]
    (B U : ℕ → C) (L V : C) (z : B 0 ≅ U 0) (t t' : L ≅ V)
    (s : ∀ n : ℕ, B (n + 1) ≅ (T.obj (B n)).obj L)
    (a : ∀ n : ℕ, (T.obj (U n)).obj V ≅ U (n + 1))
    (c : ℕ) (ht : t'.hom = c • t.hom) (d : ℕ) :
    (finiteReductionOrderedPower T B U L V z t' s a d).hom =
      c ^ d • (finiteReductionOrderedPower T B U L V z t s a d).hom := by
  induction d with
  | zero => simp only [finiteReductionOrderedPower, pow_zero, one_nsmul]
  | succ d ih =>
    simp only [finiteReductionOrderedPower, compositionTensorMapIso,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    change (s d).hom ≫ ((T.flip.obj L).map _ ≫ _) ≫ (a d).hom = _
    rw [ih, ht, Functor.map_nsmul, Functor.map_nsmul]
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, smul_smul, pow_succ, Nat.mul_comm]
    rfl

-- The fixed-scalar version of the power calculation used in
-- finiteReductionSourceTrivialization_power, before intrinsic realization.
private theorem geometricPurityFixedChart_power (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (c : ℕ) (ζ η : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η P.diagonalExponent) (hc : ζ = η ^ c)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteReductionFixedChart T d η hη M).hom =
      c ^ d • (P.finiteReductionFixedChart T d ζ hζ M).hom := by
  have hline : (P.finiteReductionShiftedLineChart T η hη).hom =
      c • (P.finiteReductionShiftedLineChart T ζ hζ).hom := by
    simp only [finiteReductionShiftedLineChart, Functor.mapIso_hom, Iso.symm_hom]
    rw [P.finiteReductionRootTrivialization_inv_power T c ζ η hζ hη hc,
      Functor.map_nsmul, Functor.map_nsmul]
  have hetale : (P.finiteReductionEtalePowerTrivialization T η hη d).hom =
      c ^ d • (P.finiteReductionEtalePowerTrivialization T ζ hζ d).hom := by
    unfold finiteReductionEtalePowerTrivialization finiteReductionEtaleRootPowerChart
      finiteReductionEtalePowerAssembly
    exact geometricPurityOrderedPower_nsmul _ _ _ _ _ _ _ _ _ _ c hline d
  have hpower : (P.finiteReductionPowerTrivialization T η hη d).hom =
      c ^ d • (P.finiteReductionPowerTrivialization T ζ hζ d).hom := by
    simp only [finiteReductionPowerTrivialization, Iso.trans_hom, Functor.mapIso_hom]
    rw [hetale, Functor.map_nsmul, Preadditive.nsmul_comp]
  have hfixed (ξ : P.field.k) (hξ : IsPrimitiveRoot ξ P.diagonalExponent) :
      P.finiteReductionFixedChart T d ξ hξ M =
        finiteReductionChartComposite P.Coefficient T M (P.diagonalTwist T d)
          (2 * (d : ℤ)) (P.finiteReductionPowerTrivialization T ξ hξ d ≪≫
            (shiftFunctor _ (2 * (d : ℤ))).mapIso
              (finiteReductionComparisonUnitChart P.Coefficient T)) :=
    eq_of_heq (P.existsUnique_finiteReductionFixedChart T d ξ hξ M).choose_spec.1
  have : ((smoothPurityTensor P.Coefficient T).obj M).Additive :=
    _root_.DerivedCategory.additive_tensorLeft M
  rw [hfixed, hfixed]
  simp only [finiteReductionChartComposite, Iso.trans_hom, Functor.mapIso_hom]
  rw [hpower, Preadditive.nsmul_comp, Functor.map_nsmul]
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp]

set_option linter.unusedSectionVars false in
/-- The root-chart expression is independent of a primitive root and fixes b uniquely.
Source: blueprint equivariance, roots-of-unity normalization
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: the roots inverse-image comparison sends the constant root zeta to gamma(zeta).
Scalar extension, ordered tensor powers and shifts give the chart expression.
Changing zeta rescales both charts by corresponding powers of the same unit in the
constant coefficient ring; gamma fixes that ring, so they cancel. Primitive roots
exist in the algebraically closed field with ell invertible. At d=0 the root factors
are the coefficient-unit comparison. Thus existence and uniqueness also hold on the
empty scheme and for the zero complex; no generator or scalar is part of the data. -/
theorem existsUnique_geometricPuritySource
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient))) :
    ∃! b :
      (P.smoothPurityPullback (P.frobeniusGaloisMap X₀)).obj
        ((P.compositionTwistShift (P.frobeniusFiber X₀).left d).obj
          ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj M)) ≅
      (P.compositionTwistShift (P.frobeniusFiber X₀).left d).obj
        ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj
          ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M)),
      ∀ (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent),
        b = P.geometricPuritySourceInChart X₀ Y₀ f₀ d M ζ hζ := by
  classical
  have hunit : IsUnit (P.diagonalExponent : P.field.k) := by
    simpa only [map_natCast] using
      (P.diagonalExponent_isUnit (𝟙 (Spec (.of P.field.k)))).map
        (Scheme.ΓSpecIso (.of P.field.k)).hom.hom
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨hunit.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  have hchart (η : P.field.k) (hη : IsPrimitiveRoot η P.diagonalExponent) :
      P.geometricPuritySourceInChart X₀ Y₀ f₀ d M ζ hζ =
        P.geometricPuritySourceInChart X₀ Y₀ f₀ d M η hη := by
    obtain ⟨c, -, hc⟩ := hη.eq_pow_of_pow_eq_one hζ.pow_eq_one
    have hγ : P.geometricPurityGamma ζ = P.geometricPurityGamma η ^ c := by
      rw [← map_pow, hc]
    let Q := P.smoothPurityPullback (P.frobeniusGaloisMap X₀)
    have : Q.Additive := inferInstanceAs
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (P.frobeniusGaloisMap X₀)).mapDerivedCategory.Additive)
    have hs := P.geometricPurityFixedChart_power d (P.frobeniusFiber X₀).left c ζ η
      hζ hη hc.symm ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj M)
    have ht := P.geometricPurityFixedChart_power d (P.frobeniusFiber X₀).left c
      (P.geometricPurityGamma ζ) (P.geometricPurityGamma η)
      (hζ.map_of_injective P.geometricPurityGamma.injective)
      (hη.map_of_injective P.geometricPurityGamma.injective) hγ
      ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj
        ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M))
    apply Iso.ext
    apply (cancel_mono (P.finiteReductionFixedChart (P.frobeniusFiber X₀).left d
      (P.geometricPurityGamma η)
      (hη.map_of_injective P.geometricPurityGamma.injective)
      ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj
        ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M))).hom).mp
    simp only [geometricPuritySourceInChart, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ht]
    simp only [Preadditive.comp_nsmul, Iso.inv_hom_id, Category.comp_id]
    rw [hs, Functor.map_nsmul]
    simp only [Preadditive.nsmul_comp]
  refine ⟨P.geometricPuritySourceInChart X₀ Y₀ f₀ d M ζ hζ, hchart, ?_⟩
  intro b hb
  exact hb ζ hζ

/-- The uniquely normalized b_K, constructed independently of purity and its mate.
Source: blueprint equivariance, b_K
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPuritySource
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient))) :=
  (P.existsUnique_geometricPuritySource X₀ Y₀ f₀ d M).choose

private theorem geometricPurityCtfOfIso (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) {K L : Scheme.proEtaleDerivedCategory T P.Ring} (e : K ≅ L)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T L := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
        P.level_pos T) := (Scheme.proEtale_bounded_constructible_isTriangulated T P.Ring).1
  refine ⟨ObjectProperty.prop_of_iso _ e hK.1, ?_⟩
  obtain ⟨a, b, ht⟩ := hK.2
  refine ⟨a, b, ht.1, ?_⟩
  intro C Q hC g hg hQ N i hi
  exact ht.2 C Q (hC.map (fun j ↦ j ≪≫ e.symm)) g hg hQ N i hi

private def geometricPurityPullbackRealization (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Scheme.proEtaleConstantRingDerivedPullback P.Ring g ≅
      (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse ⋙
        P.smoothPurityPullback g ⋙
          (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor := by
  have : (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor.Additive :=
    ProEtale.finiteCoefficientIntrinsicRealization_additive X P.Ring
  exact Scheme.openSquareDerivedPullbackModel P.Ring g ≪≫
    Functor.mapDerivedCategoryCompIso
      (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).inverse
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g ⋙
        (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)

/-- Geometric inverse image preserves bounded constructibility and finite Tor amplitude.
Source: blueprint equivariance, domain of PK
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: g_Y is a scheme isomorphism, hence an equivalence of the small sites. This
carries finite stratifications, finite locally constant presentations, bounds on
cohomology, and the tensor tests for Tor amplitude to exactly the same tests.
The canonical realization equivalence does not change those properties. -/
theorem geometricPurityInput
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left
      ((Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj M)) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left
      ((Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj
        ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M)) := by
  let γ := P.geometricPurityRetagFrobenius Y₀
  have hγ := P.field.galoisMap_inverse Y₀.hom P.geometricPurityGamma
  let eγ : (P.frobeniusFiber Y₀).left ≅ (P.frobeniusFiber Y₀).left :=
    ⟨P.frobeniusGaloisMap Y₀,
      P.field.galoisMap Y₀.hom P.geometricPurityGamma.symm, hγ.1, hγ.2⟩
  have : IsIso γ.left := eγ.isIso_hom
  have h := sf_pullback_finiteTorConstructible P.field P.coefficients.l
    P.coefficients.different P.extension P.level P.level_pos
    (P.geometricPurityRetag Y₀) (P.frobeniusFiber Y₀) γ
    ((Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj M)
    hM
  let E := Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring
  let e := (P.geometricPurityPullbackRealization γ.left).app (E.functor.obj M) ≪≫
    E.functor.mapIso ((P.smoothPurityPullback γ.left).mapIso (E.unitIso.app M).symm)
  exact P.geometricPurityCtfOfIso _ e h

/-- Bounded finite-Tor constructible inputs have a bounded etale presentation.
Source: finite-ring constructible comparison
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: finiteRing_constructibleDerived_origin gives a bounded etale representative
of the intrinsic realization. Undo that equivalence, using its unit isomorphism.
The representative's finite cohomological interval gives its lower bound. -/
theorem geometricPurityOrigin (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
      ((Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor.obj M)) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) T M := by
  classical
  let E := Scheme.sfIntrinsicDerivedEquivalence T P.Ring
  let K := E.functor.obj M
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
  let R := ProEtale.finiteCoefficientIntrinsicRealization T P.Ring
  have : R.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive T P.Ring
  have : PreservesFiniteLimits R :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits T P.Ring
  have : PreservesFiniteColimits R :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits T P.Ring
  obtain ⟨a, ha⟩ := hM.1.1.bddBelow
  obtain ⟨b, hb⟩ := hM.1.1.bddAbove
  have hz (i : ℤ) (hi : i < min a b ∨ max a b < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    by_contra hn
    have ha' := ha hn
    have hb' := hb hn
    rcases hi with hi | hi <;> omega
  obtain ⟨J, ⟨eJ⟩⟩ :=
    ((Scheme.finiteRing_constructibleDerived_origin T P.Ring).2.2.1 K).mpr
      ⟨hM.1.2, min a b, max a b, min_le_max, hz⟩
  let eCJ : E.functor.obj (C.mapDerivedCategory.obj J.obj) ≅ K :=
    ((Functor.mapDerivedCategoryCompIso C R).app J.obj).symm ≪≫ eJ
  let e : C.mapDerivedCategory.obj J.obj ≅ M :=
    E.unitIso.app _ ≪≫ E.inverse.mapIso eCJ ≪≫ (E.unitIso.app M).symm
  obtain ⟨c, d, _, hv⟩ := J.property.2
  exact ⟨J.obj, ⟨c, (DerivedCategory.isGE_iff J.obj c).mpr
    (fun i hi ↦ hv i (.inl hi))⟩, ⟨e⟩⟩

/-- Exact inverse image preserves bounded etale origin.
Source: canonical etale/pro-etale pullback square
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: pull back a bounded etale representative termwise and use the canonical
comparison-upper-star compositor. Exactness preserves its lower bound. -/
theorem geometricPurityPullbackOrigin (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) Y M) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X
      ((P.smoothPurityPullback g).obj M) := by
  obtain ⟨N, ⟨a, ha⟩, ⟨e⟩⟩ := hM
  refine ⟨(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).mapDerivedCategory.obj N,
    ⟨a, (Etale.upperStar _ g).isGE_mapDerivedCategory_obj N a⟩, ⟨?_⟩⟩
  exact ((ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) g).app N).symm ≪≫
      (P.smoothPurityPullback g).mapIso e

/-- The specified compact-support exchange is invertible on bounded etale origin.
Source: finite compact-support base change
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: inverse image preserves etale origin. The exact/derived comparison gives the
origin test selecting the nonzero branch of B. Its proper/open base-change factor
and compactification comparison are isomorphisms, as are its coordinate factors. -/
theorem geometricPurityBIsIsoOfOrigin (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (gX : X ⟶ X) (gY : Y ⟶ Y) (sq : IsPullback gX f f gY)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) X M) :
    IsIso (P.geometricPurityB f aY gX gY sq M) := by
  have hq : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) X
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) gX).leftDerivedFunctor.obj M) :=
    ObjectProperty.prop_of_iso _
      ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) gX).app M).symm
      (P.geometricPurityPullbackOrigin gX M hM)
  have := ProEtale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    P.Coefficient sq (P.geometricPurityCompactification f aY) M hM
  dsimp only [geometricPurityB]
  rw [dif_pos hq]
  infer_instance

/-- The specified B is invertible on the stated bounded constructible finite-Tor domain.
Source: blueprint equivariance, compact-support base change
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: the quotient A is finite and ell^n annihilates it, including ramified E.
Proper finite-coefficient base change makes the proper factor invertible on
bounded-below etale-origin objects; open exchange is invertible. The canonical
compactification comparison is invertible on that same class. A finite-Tor
constructible input is in this class, as is its inverse image by g_X. The fixed
pullback comparisons conjugating the published exchange are isomorphisms. -/
theorem geometricPurityBIsIso
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber X₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber X₀).left
      ((Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber X₀).left P.Ring).functor.obj M)) :
    IsIso (P.geometricPurityB (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
      (P.frobeniusGaloisMap X₀) (P.frobeniusGaloisMap Y₀)
      (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1 M) := by
  exact P.geometricPurityBIsIsoOfOrigin _ _ _ _ _ M
    (P.geometricPurityOrigin _ M hM)

/-- The counit equation uniquely determines e_K. Since B at G K is invertible, this
is exactly the adjoint transpose of P(epsilon_K) after B_(G K)^-1.
Source: blueprint equivariance, definition of e_K
(blueprint: def-pur-finite-geometric-purity-coordinates).
Proof: the exceptional functor preserves the constructible finite-Tor class. Apply
compact-support base change at G K and the standing relative Hom bijection at
Q G K and P K. Its inverse is F(-) followed by the canonical counit. Multiplying
by B identifies its defining equation with the displayed equation, and injectivity
of that Hom bijection proves uniqueness. No ambient pro-etale adjoint is assumed. -/
theorem existsUnique_geometricPurityMate
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left
      ((Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj M)) :
    ∃! e :
      (P.smoothPurityPullback (P.frobeniusGaloisMap X₀)).obj
        ((P.smoothPurityExceptionalOver (P.frobeniusMap f₀)
          (P.frobeniusFiber Y₀).hom).obj M) ⟶
      (P.smoothPurityExceptionalOver (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom).obj
        ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M),
      P.geometricPurityB (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
          (P.frobeniusGaloisMap X₀) (P.frobeniusGaloisMap Y₀)
          (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1
          ((P.smoothPurityExceptionalOver (P.frobeniusMap f₀)
            (P.frobeniusFiber Y₀).hom).obj M) ≫
        (P.geometricPurityF (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom).map e ≫
        P.geometricPurityCounit (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
          ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M) =
      (P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).map
        (P.geometricPurityCounit (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom M) := by
  let f := P.frobeniusMap f₀
  let aY := (P.frobeniusFiber Y₀).hom
  let := isNoetherian_of_locallyOfFiniteType aY
  let := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  let : CompactSpace (P.frobeniusFiber Y₀).left :=
    QuasiCompact.compactSpace_of_compactSpace aY
  let : HasCompactification f := inferInstance
  let F := P.geometricPurityF f aY
  let G := P.smoothPurityExceptionalOver f aY
  let Q := P.smoothPurityPullback (P.frobeniusGaloisMap X₀)
  let R := P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)
  have hOrigin := P.geometricPurityOrigin _ M hM
  have hplus := hOrigin.plus
  have hRplus := (P.geometricPurityPullbackOrigin
    (P.frobeniusGaloisMap Y₀) M hOrigin).plus
  have hG : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber X₀).left (G.obj M) :=
    ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj f hplus
  have hQG := P.geometricPurityPullbackOrigin (P.frobeniusGaloisMap X₀) (G.obj M) hG
  let B := P.geometricPurityB f aY (P.frobeniusGaloisMap X₀)
    (P.frobeniusGaloisMap Y₀)
    (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1 (G.obj M)
  have : IsIso B := P.geometricPurityBIsIsoOfOrigin _ _ _ _ _ (G.obj M) hG
  let H : (F.obj (Q.obj (G.obj M)) ⟶ R.obj M) ≃
      (Q.obj (G.obj M) ⟶ G.obj (R.obj M)) :=
    ProEtale.rightDerivedUpperShriekHomEquiv f hQG hRplus
  let t := R.map (P.geometricPurityCounit f aY M)
  let e := H (inv B ≫ t)
  have he : F.map e ≫ P.geometricPurityCounit f aY (R.obj M) = inv B ≫ t := by
    have hh := H.symm_apply_apply (inv B ≫ t)
    change (ProEtale.rightDerivedUpperShriekHomEquiv f hQG hRplus).symm e = _ at hh
    rw [ProEtale.rightDerivedUpperShriekHomEquiv_symm_apply] at hh
    dsimp only [geometricPurityCounit]
    rw [dif_pos hRplus]
    exact hh
  refine ⟨e, ?_, ?_⟩
  · change B ≫ F.map e ≫ P.geometricPurityCounit f aY (R.obj M) = t
    rw [he]
    simp
  · intro e' he'
    apply H.symm.injective
    change H.symm e' = H.symm (H (inv B ≫ t))
    rw [H.symm_apply_apply]
    change F.map e' ≫ ProEtale.rightDerivedUpperShriekCounit f (R.obj M) hRplus = _
    change B ≫ F.map e' ≫ P.geometricPurityCounit f aY (R.obj M) = t at he'
    have he'' : F.map e' ≫ P.geometricPurityCounit f aY (R.obj M) = inv B ≫ t := by
      apply (cancel_epi B).mp
      simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using he'
    dsimp only [geometricPurityCounit] at he''
    rw [dif_pos hRplus] at he''
    exact he''

/-- The canonical counit mate. Choice extracts only the uniquely specified arrow.
Source: blueprint equivariance, e_K
(blueprint: def-pur-finite-geometric-purity-coordinates). -/
def geometricPurityMate
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left
      ((Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj M)) :=
  (P.existsUnique_geometricPurityMate X₀ Y₀ f₀ M hM).choose

end Frobenius
end WeilConjectures.PurityFiniteSetting
