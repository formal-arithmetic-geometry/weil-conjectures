/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.DeligneLaumon.CondensedFieldSmoothDuality
-- Construction-only dependency: def-zl-condensed-field-duality-constructions.
public import WeilConjectures.AlgebraicGeometry.CondensedConstantExtensionFrobenius
public import WeilConjectures.SixFunctors.FrobeniusPointTransport
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SecSmoothPurity.TransportLinePull
public import WeilConjectures.SecSmoothPurity.TransportCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections

import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.SitePerfectDualizableHom
import WeilConjectures.AlgebraicGeometry.CondensedWeilEquivarianceParent
import WeilConjectures.AlgebraicGeometry.GlobalVerdierDuality
import WeilConjectures.SecSmoothPurity.TraceBasic
import WeilConjectures.AlgebraicGeometry.ProperCompactCoincidence
import WeilConjectures.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent
import WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import WeilConjectures.AlgebraicGeometry.ProperCoincidenceFrobenius
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Poincare pairing on possibly disconnected smooth proper fibres

Source: latest blueprint, sec-zeta-weil/sk-prop-smooth-proper-purity/
prop-zl-smooth-proper-relative-purity.proof.md, Step 3
(blueprint: lem-zl-disconnected-fibre-poincare-pairing).

The pairing uses actual condensed modules, their relative derived coefficient dual,
the root-normalized Tate line and the normalized smooth trace. Scalar coordinates
use the canonical universe lift of Qbar_l. No component is required to descend to
the finite field, and no connectedness or nonemptiness is assumed on the fibre.

## Main definitions

- `nativePairing`: the canonical trace-evaluation pairing before scalar evaluation.
- `Components`: a finite clopen partition by geometric connected components.
- `sections`: ordinary derived sections in the canonical lifted scalar coordinates.
- `twistedPhi`: the recorded twisted contragredient Weil isomorphism.

## Main statements

- `disconnected_fibre_poincare_pairing`: componentwise sum, perfectness and invariance.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.DisconnectedFibrePoincare

/-- Actual condensed coefficient modules.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev M (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :=
  FieldSmoothDuality.coefficientModule ell X

/-- The ordinary unbounded derived category of these modules.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev C (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) := DerivedCategory (M ell X)

/-- Relative derived coefficient dual, using the recorded closed structure.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev dual (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (K : C ell X) :=
  StrictWeil.dual (Profinite.padicAlgClRingObj ell) K

/-- The actual positive Tate line from the recorded root construction, in degree zero.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev line (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) (d : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (PurityTransport.Coefficient.closure.line ell X d)

/-- The unshifted actual twisted derived dual.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev twistedDual (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (K : C ell X) (d : ℕ) :=
  dual ell K ⊗ line ell X d

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Derived evaluation tensored with the actual Tate line.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def evaluation (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (K : C ell X) (d : ℕ) :
    K ⊗ twistedDual ell K d ⟶ line ell X d :=
  (α_ K (dual ell K) (line ell X d)).inv ≫
    ((ihom.ev K).app (𝟙_ _) ▷ line ell X d) ≫ (λ_ _).hom

/-- Exact inverse image in the recorded condensed coefficient category.
Source: latest blueprint, component restriction
(blueprint: lem-zl-disconnected-fibre-poincare-pairing).
-/
abbrev pull (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (Profinite.padicAlgClRingObj ell) f).mapDerivedCategory

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The exact-pullback/total-direct-image adjunction, with its canonical comparison.
Source: latest blueprint, cup product (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def adj (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ell) f).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ell) f)

/-- Ordinary derived direct image on the actual module category.
Source: latest blueprint, RΓ (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev push (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (Profinite.padicAlgClRingObj ell) f).rightDerivedFunctor

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The exact-derived tensorator is transported from the canonical K-flat pullback.
Source: latest blueprint, monoidal restriction
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
instance pullMonoidal (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull ell f).Monoidal :=
  Functor.Monoidal.transport
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ell) f)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The ordinary cup product, the tensor-adjoint of the two inverse-image counits.
Source: latest blueprint, trace-evaluation pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def cup (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : C ell X) : (push ell f).obj K ⊗ (push ell f).obj L ⟶
      (push ell f).obj (K ⊗ L) :=
  (adj ell f).homEquiv _ _
    ((Functor.Monoidal.μIso (pull ell f) _ _).inv ≫
      ((adj ell f).counit.app K ⊗ₘ (adj ell f).counit.app L))

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Identity-open compactification gives the canonical proper comparison, by uniqueness
of the left adjoint of identity inverse image.
Source: latest blueprint, H_c = H (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def properComparison (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] : rightDerivedLowerShriekOfCompactification
      (Profinite.padicAlgClRingObj ell) (Compactification.ofIsProper f) ≅
      push ell f :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (((openImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ell) (𝟙 X)).ofNatIsoRight
          (upperStarId (Profinite.padicAlgClRingObj ell) X)).leftAdjointUniq Adjunction.id) ≪≫
      Functor.mapDerivedCategoryIdIso _) (push ell f) ≪≫ Functor.leftUnitor _

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The two positive root-tower presentations agree by their defining tensor recursion.
Source: latest blueprint, actual Tate line
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def lineComparison (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) (d : ℕ) :
    line ell X d ≅ tateTwistDerived X ell d :=
  (DerivedCategory.singleFunctor _ 0).mapIso (eqToIso (by
    change PurityTransport.Coefficient.closure.line ell X d = tateTwistNat X ell d
    induction d with
    | zero => rfl
    | succ d ih =>
        change PurityTransport.Coefficient.closure.line ell X d ⊗
          PurityTransport.Coefficient.closure.firstLine ell X =
            tateTwistNat X ell d ⊗ tateTwistOne X ell
        rw [ih]
        rfl))

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Normalized smooth trace, read on ordinary direct image using identity-open coincidence.
Source: latest blueprint, trace-evaluation pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def trace (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k))) [IsProper X.hom] (d : ℕ) :
    (push ell X.hom).obj ((line ell X.left d) ⟦2 * (d : ℤ)⟧) ⟶
      𝟙_ (C ell (Spec (.of k))) :=
  (push ell X.hom).map
    ((shiftFunctor _ (2 * (d : ℤ))).map (lineComparison ell X.left d).hom) ≫
    (properComparison ell X.hom).inv.app _ ≫
    FieldSmoothDuality.orientedTrace ell X (Compactification.ofIsProper X.hom) d

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Cup, evaluation, the even shift comparison, and the normalized smooth trace.
The displayed evaluation can also be a restriction to a geometric component.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def nativePairing (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k))) [IsProper X.hom] (d : ℕ)
    (K L : C ell X.left) (e : K ⊗ L ⟶ line ell X.left d) :
    (push ell X.hom).obj K ⊗ ((push ell X.hom).obj L) ⟦2 * (d : ℤ)⟧ ⟶
      𝟙_ (C ell (Spec (.of k))) :=
  ((tensorLeft _).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      (cup ell X.hom K L ≫ (push ell X.hom).map e) ≫
    ((push ell X.hom).commShiftIso (2 * (d : ℤ))).inv.app _ ≫ trace ell X d

/-- Canonical lifted Qbar coordinates, so ring and module universes agree for tensor.
Source: latest blueprint, scalar modules (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev Scalar (ell : ℕ) [Fact ell.Prime] := CohomologyScalar.{u} ell

/-- Ordinary scalar-module category, without any condensed coefficients in its objects.
Source: latest blueprint, scalar modules (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev V (ell : ℕ) [Fact ell.Prime] := ModuleCat.{u + 1} (Scalar.{u} ell)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The locally small scalar derived category size, shared with exact point evaluation.
Source: latest blueprint, scalar modules (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
instance scalarDerived (ell : ℕ) [Fact ell.Prime] : HasDerivedCategory.{u + 1} (V.{u} ell) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- Ordinary scalar derived category with locally small morphisms.
Source: latest blueprint, scalar modules (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev DScalar (ell : ℕ) [Fact ell.Prime] := DerivedCategory (V.{u} ell)

/-- The canonical lifted scalar version of exact geometric-field evaluation.
Source: latest blueprint, scalar RΓ (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev pointSections (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k] :=
  (CondensedQbarGeometricEvaluation.fieldFiber k ell ⋙
    ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : Scalar.{u} ell →+* PadicAlgCl ell)).mapDerivedCategory

/-- Ordinary scalar sections, using exactly the published direct image and point evaluation.
Source: latest blueprint, scalar RΓ (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev sections (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) := push ell a ⋙ pointSections ell k


/-- Evaluation on coefficient modules, in the canonical universe lift.
Source: latest blueprint, scalar coordinates
(blueprint: lem-zl-disconnected-fibre-poincare-pairing).
-/
abbrev pointHeart (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k] :=
  CondensedQbarGeometricEvaluation.fieldFiber k ell ⋙
    ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : Scalar.{u} ell →+* PadicAlgCl ell)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The constant-section coordinates after the canonical scalar lift.
Source: latest blueprint, scalar target (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def pointUnitHeart (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] :
    (pointHeart ell k).obj (𝟙_ (M ell (Spec (.of k)))) ≃ₗ[Scalar.{u} ell] Scalar.{u} ell where
  toFun x := ULift.up (CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell x)
  invFun x := (CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).symm x.down
  left_inv x := (CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).symm_apply_apply x
  right_inv x := congrArg ULift.up
    ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).apply_symm_apply x.down)
  map_add' x y := congrArg ULift.up
    ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).map_add x y)
  map_smul' a x := congrArg ULift.up
    ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).map_smul a.down x)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The canonical scalar-unit comparison; it sends the constant coefficient section to itself.
Source: latest blueprint, scalar target (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def pointUnit (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k] :
    (pointSections ell k).obj (𝟙_ (C ell (Spec (.of k)))) ≅ 𝟙_ (DScalar.{u} ell) :=
  (pointSections ell k).mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((pointHeart ell k).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (pointUnitHeart ell k).toModuleIso ≪≫ DerivedCategory.singleFunctorObjUnitIso _

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The scalar derived class of a native class, with its unit and shift comparisons.
Source: latest blueprint, induced degreewise pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def scalarClass (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    {P : C ell (Spec (.of k))} (r : ℤ) (x : 𝟙_ _ ⟶ P ⟦r⟧) :
    𝟙_ (DScalar.{u} ell) ⟶ ((pointSections ell k).obj P) ⟦r⟧ :=
  (pointUnit ell k).inv ≫ (pointSections ell k).map x ≫
    ((pointSections ell k).commShiftIso r).hom.app P

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- An endomorphism of the scalar derived unit, in its specified Qbar coordinates.
Source: latest blueprint, scalar target (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def scalarValue (ell : ℕ) [Fact ell.Prime] (f : End (𝟙_ (DScalar.{u} ell))) :
    Scalar.{u} ell :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso (V.{u} ell) 0).inv.app (𝟙_ (V.{u} ell)) ≫
    (DerivedCategory.homologyFunctor (V.{u} ell) 0).map
      ((DerivedCategory.singleFunctorObjUnitIso _).hom ≫ f ≫
        (DerivedCategory.singleFunctorObjUnitIso _).inv) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (V.{u} ell) 0).hom.app _).hom
      (1 : Scalar.{u} ell)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Evaluation of a scalar derived pairing on complementary shifted classes.
All tensor shifts are the recorded derived shift comparisons, including their signs.
Source: latest blueprint, induced degreewise pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def scalarDegree (ell : ℕ) [Fact ell.Prime] (P Q : DScalar.{u} ell) (n r : ℤ)
    (b : P ⊗ Q ⟦n⟧ ⟶ 𝟙_ _) (x : 𝟙_ _ ⟶ P ⟦r⟧) (y : 𝟙_ _ ⟶ Q ⟦n - r⟧) :
    Scalar.{u} ell :=
  scalarValue ell ((λ_ (𝟙_ _)).inv ≫
    (x ⊗ₘ (y ≫ ((shiftFunctorAdd' _ n (-r) (n - r) (sub_eq_add_neg n r)).app Q).hom)) ≫
    (DerivedCategory.shiftTensorShiftIso _ P (Q ⟦n⟧) r (-r)).hom ≫
    (shiftFunctor _ (r + -r)).map b ≫
    eqToHom (congrArg (fun j : ℤ ↦ (𝟙_ (DScalar.{u} ell)) ⟦j⟧) (add_neg_cancel r)) ≫
    (shiftFunctorZero _ ℤ).hom.app _)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Cohomology class of a derived scalar-unit map, by the single and homology comparisons.
Source: latest blueprint, H^i (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def homologyClass (ell : ℕ) [Fact ell.Prime] {P : DScalar.{u} ell} (r : ℤ)
    (x : 𝟙_ _ ⟶ P ⟦r⟧) : (DerivedCategory.homologyFunctor (V.{u} ell) r).obj P :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso (V.{u} ell) 0).inv.app (𝟙_ (V.{u} ell)) ≫
    (DerivedCategory.homologyFunctor (V.{u} ell) 0).map
      ((DerivedCategory.singleFunctorObjUnitIso _).hom ≫ x) ≫
    ((DerivedCategory.homologyFunctor (V.{u} ell) 0).shiftIso r 0 r (add_zero r)).hom.app P).hom
      (1 : Scalar.{u} ell)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Restriction of ordinary direct image, the direct-image unit followed by composition.
Source: latest blueprint, geometric components
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def restriction (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    {U X : Over (Spec (.of k))} (j : U ⟶ X) (K : C ell X.left) :
    (push ell X.hom).obj K ⟶ (push ell U.hom).obj ((pull ell j.left).obj K) :=
  (push ell X.hom).map ((adj ell j.left).unit.app K) ≫
    (PurityTransport.lowerComp (Profinite.padicAlgClRingObj ell) j.left X.hom).inv.app _ ≫
    (eqToIso (congrArg (push ell) j.w)).hom.app _

/-- A finite clopen partition by geometric connected components. The zero-component
partition is available precisely for an empty scheme. Its pieces live over k, not k_0.
Source: latest blueprint, disconnected fibre
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
structure Components {k : Type u} [Field k] (X : Over (Spec (.of k))) (d : ℕ) where
  n : ℕ
  piece : Fin n → Over (Spec (.of k))
  inclusion : ∀ i, piece i ⟶ X
  [openPiece : ∀ i, IsOpenImmersion (inclusion i).left]
  [closedPiece : ∀ i, IsClosedImmersion (inclusion i).left]
  [connected : ∀ i, ConnectedSpace (piece i).left]
  [proper : ∀ i, IsProper (piece i).hom]
  [smooth : ∀ i, SmoothOfRelativeDimension d (piece i).hom]
  disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (inclusion i).left) (Set.range (inclusion j).left)
  cover : (⋃ i, Set.range (inclusion i).left) = Set.univ

attribute [instance] Components.openPiece Components.closedPiece Components.connected
  Components.proper Components.smooth

set_option maxHeartbeats 8000000 in
-- Keep the coefficient abstract while checking its exact-derived single comparison.
/-- Derived restriction of a root-normalized positive Tate power. Keeping the coefficient
abstract retains exactly the published tensor-power comparison without expanding its ring.
Source: latest blueprint, component Tate restriction
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def powerRestriction (ell : ℕ) [Fact ell.Prime]
    (c : PurityTransport.Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (t : PurityTransport.LinePullCoordinates ell c f) :
    (upperStar (c.obj ell) f).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (c.line ell Y d)) ⟶
        (DerivedCategory.singleFunctor _ 0).obj (c.line ell X d) :=
  ((upperStar (c.obj ell) f).mapDerivedCategorySingleFunctor 0).hom.app (c.line ell Y d) ≫
    (DerivedCategory.singleFunctor _ 0).map (t.power d).hom

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Restrict evaluation and the actual Tate line using the root-normalized pullback.
The line coordinate is supplied with its published projection normalization in the theorem.
Source: latest blueprint, component trace-evaluation
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def restrictEvaluation (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    {U X : Over (Spec (.of k))} (j : U ⟶ X) (K : C ell X.left) (d : ℕ)
    (t : PurityTransport.LinePullCoordinates ell PurityTransport.Coefficient.closure j.left) :
    (pull ell j.left).obj K ⊗ (pull ell j.left).obj (twistedDual ell K d) ⟶
      line ell U.left d :=
  (Functor.Monoidal.μIso (pull ell j.left) _ _).hom ≫
    (pull ell j.left).map (evaluation ell K d) ≫
    powerRestriction ell PurityTransport.Coefficient.closure j.left d t

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Properness of the geometric fibre is the standard base-change instance.
Source: latest blueprint, Z = Z_0 times k
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
instance fibreProper (D : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of D.k₀)))
    [IsProper X₀.hom] : IsProper (D.geometricFiber X₀).hom :=
  inferInstanceAs (IsProper (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Scalar ordinary Frobenius, from point insertion, direct-image exchange, then the given
Weil isomorphism. It works for the sheaf and the ambient twisted derived dual alike.
Source: latest blueprint, geometric Frobenius
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def frobenius (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (K : C ell (D.geometricFiber X₀).left)
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D X₀)).obj K ≅ K) :
    End ((sections ell (D.geometricFiber X₀).hom).obj K) :=
  (pointSections ell D.k).map
    ((CondensedWeil.derivedPointInsertion ell D.k (WeilConjectures.frobeniusPointIso D).hom
      (𝟭 _)).hom.app _ ≫
    (constantExtensionProperExchange (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber X₀).hom (D.geometricFrobenius X₀)
      (WeilConjectures.frobeniusPointIso D) (CondensedWeil.structureSquare D X₀)).app K ≫
    (push ell (D.geometricFiber X₀).hom).map phi.hom)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Frobenius on scalar cohomology in any integer degree.
Source: latest blueprint, geometric Frobenius
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def cohomologyFrobenius (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (K : C ell (D.geometricFiber X₀).left)
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D X₀)).obj K ≅ K) (i : ℤ) :=
  (DerivedCategory.homologyFunctor (V.{u} ell) i).map (frobenius D ell X₀ K phi)

/-- The coefficient prime is invertible at every geometric point; this is inherited
from ell != p and is not a hypothesis restricting the allowed schemes.
Source: latest blueprint, standing characteristic hypothesis
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev primeInvertible (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X : Over (Spec (.of D.k))) (x : X.left) :
    Invertible (ell : X.left.residueField x) :=
  (by simpa only [map_natCast] using
    (PurityTransport.primeUnit D ell hEll).map (X.hom.residueFieldAlgebraMap x) :
      IsUnit (ell : X.left.residueField x)).invertible

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The derived structure on F-dual(d) is exactly the recorded contragredient tensor
root-normalized Tate datum. No choice of an inverse Frobenius operator is introduced.
Source: latest blueprint, contragredient and twist
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def twistedPhi (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (K : C ell (D.geometricFiber X₀).left)
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D X₀)).obj K ≅ K) (d : ℕ) :
    (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D X₀)).obj (twistedDual ell K d) ≅
        twistedDual ell K d :=
  letI := primeInvertible D ell hEll (D.geometricFiber X₀)
  StrictWeil.twistedDualDatum ell PurityTransport.Coefficient.closure
    (StrictWeil.modelFrobenius D X₀) K phi d

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The canonical pairing on this finite-field geometric fibre, before scalar evaluation.
Source: latest blueprint, trace-evaluation pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def fibrePairing (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X : Over (Spec (.of D.k))) [IsProper X.hom]
    (d : ℕ) (K L : C ell X.left) (e : K ⊗ L ⟶ line ell X.left d) :=
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hEll.symm⟩
  nativePairing ell X d K L e

/-- The bilinear degreewise family of a scalar derived pairing.
Source: latest blueprint, all integer degrees
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev Pairings (ell : ℕ) [Fact ell.Prime] (P Q : DScalar.{u} ell) (d : ℕ) :=
  ∀ i : ℤ, (DerivedCategory.homologyFunctor (V.{u} ell) i).obj P →ₗ[Scalar.{u} ell]
    (DerivedCategory.homologyFunctor (V.{u} ell) (2 * (d : ℤ) - i)).obj Q →ₗ[Scalar.{u} ell]
      Scalar.{u} ell

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The induced pairing is specified on every scalar cohomology class, so it cannot
be an unrelated perfect pairing. These are the actual ordinary scalar cohomology spaces.
Source: latest blueprint, induced degreewise pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def IsInducedPairing (ell : ℕ) [Fact ell.Prime] (P Q : DScalar.{u} ell) (d : ℕ)
    (b : P ⊗ Q ⟦2 * (d : ℤ)⟧ ⟶ 𝟙_ _) (B : Pairings ell P Q d) : Prop :=
  ∀ (i : ℤ) (x : 𝟙_ _ ⟶ P ⟦i⟧) (y : 𝟙_ _ ⟶ Q ⟦2 * (d : ℤ) - i⟧),
    B i (homologyClass ell i x) (homologyClass ell (2 * (d : ℤ) - i) y) =
      scalarDegree ell P Q (2 * (d : ℤ)) i b x y

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Scalar descent is fixed in every degree by the actual native cup/evaluation/trace
pairing, not by an arbitrary duality isomorphism. Over the coefficient field all complexes
split into their cohomology, so these equations determine the derived pairing uniquely.
Source: latest blueprint, scalar adjoint
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def IsScalarNormalizedPairing (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k]
    (P Q : C ell (Spec (.of k))) (d : ℕ)
    (b : P ⊗ Q ⟦2 * (d : ℤ)⟧ ⟶ 𝟙_ _)
    (bs : (pointSections ell k).obj P ⊗ ((pointSections ell k).obj Q) ⟦2 * (d : ℤ)⟧ ⟶
      𝟙_ (DScalar.{u} ell)) : Prop :=
  ∀ (i : ℤ) (x : 𝟙_ _ ⟶ P ⟦i⟧) (y : 𝟙_ _ ⟶ Q ⟦2 * (d : ℤ) - i⟧),
    scalarDegree ell _ _ (2 * (d : ℤ)) i bs
      (scalarClass ell k i x) (scalarClass ell k (2 * (d : ℤ) - i) y) =
        FieldSmoothDuality.degreePairing ell k P Q (2 * (d : ℤ)) i b x y

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Condensed Poincare duality for possibly disconnected smooth proper geometric fibres.
The component identity uses geometric components over k and the canonical restriction maps.
The scalar pairing is normalized by cup/evaluation/trace in all degrees. Its transpose is
invertible and its induced bilinear pairings are perfect, finite-dimensional and invariant
under the given geometric Frobenius and the root-normalized twisted contragredient.

Source: latest blueprint, sec-zeta-weil/sk-prop-smooth-proper-purity/
prop-zl-smooth-proper-relative-purity.proof.md, Step 3
(blueprint: lem-zl-disconnected-fibre-poincare-pairing).

Proof plan, following the seven steps of the DAG node:
1. Lisse means locally finite free, including rank zero. These local models give one-stratum
constructibility, Tor interval [0,0] and site-perfectness. The canonical coefficient-dual
comparison of prop-sf-dualizable-hom, followed by sk-thm-purity-transport, identifies the
Verdier dual with the evaluation-compatible F-dual(d)[2d].
2. Apply sk-thm-sf-global-duality to all of Z. Its adjoint is cup, evaluation and the
exceptional counit. det-sp-trace-basic identifies that counit with normalized smooth trace;
prop-weil-proper-compact-coincidence identifies ordinary and compact sections.
3. Finite type over a Noetherian point and finitely many irreducible components give a finite
clopen connected-component partition by grouping intersecting irreducible components.
Each piece is smooth of dimension d and proper; it need not descend to k_0.
4. lem-pur-clopen-unbounded-derived-localization and lem-pur-clopen-kflat-monoidal-descent
split the complexes and evaluation. Cross terms vanish. Trace transitivity
(thm-pur-trace-normalization-transitivity) and the finite-etale summation clause of
det-sp-trace-basic identify each supported trace with its component trace. Thus the pairing
is the displayed finite sum, independently of any ordering.
5. The section complexes are perfect over the field. Apply
lem-pod-cohomology-of-dual-over-field in degree -i. Since H^(-i)(B[2d]) is H^(2d-i)(B),
the induced bilinear pairing has both adjoints bijective and both factors finite-dimensional.
6. In evaluation the inverse Weil isomorphism in the contravariant Hom slot cancels the
original one. Tensor with the canonical Tate datum. prop-weil-operations and
thm-pur-weil-equivariance-of-purity-and-trace make the cup and normalized trace equivariant;
lem-pod-proper-coincidence-frobenius identifies ordinary and supported operators. The target
has trivial action and the second factor includes q^(-d) by sk-def-sf-weil-complexes.
7. If Z is empty its component set is empty. Clopen localization makes its category zero;
all section complexes and cohomology vanish. The empty sum is zero and its adjoint is the
isomorphism between zero objects, so no nonempty-fibre exception is needed.
-/
theorem disconnected_fibre_poincare_pairing
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom]
    (F : M ell (D.geometricFiber X₀).left)
    (_hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) F)
    (phi : (StrictWeil.action (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D X₀)).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
        (DerivedCategory.singleFunctor _ 0).obj F) :
    (∃ (A : Components (D.geometricFiber X₀) d)
      (t : ∀ i, PurityTransport.LinePullCoordinates ell PurityTransport.Coefficient.closure
        (A.inclusion i).left),
      fibrePairing D ell hEll (D.geometricFiber X₀) d
          ((DerivedCategory.singleFunctor _ 0).obj F)
          (twistedDual ell ((DerivedCategory.singleFunctor _ 0).obj F) d)
          (evaluation ell ((DerivedCategory.singleFunctor _ 0).obj F) d) =
        ∑ i, (restriction ell (A.inclusion i) ((DerivedCategory.singleFunctor _ 0).obj F) ⊗ₘ
          (shiftFunctor _ (2 * (d : ℤ))).map
            (restriction ell (A.inclusion i)
              (twistedDual ell ((DerivedCategory.singleFunctor _ 0).obj F) d))) ≫
          fibrePairing D ell hEll (A.piece i) d
            ((pull ell (A.inclusion i).left).obj ((DerivedCategory.singleFunctor _ 0).obj F))
            ((pull ell (A.inclusion i).left).obj
              (twistedDual ell ((DerivedCategory.singleFunctor _ 0).obj F) d))
            (restrictEvaluation ell (A.inclusion i) ((DerivedCategory.singleFunctor _ 0).obj F)
              d (t i))) ∧
    ∃ (b : (sections ell (D.geometricFiber X₀).hom).obj
        ((DerivedCategory.singleFunctor _ 0).obj F) ⊗
          ((sections ell (D.geometricFiber X₀).hom).obj
            (twistedDual ell ((DerivedCategory.singleFunctor _ 0).obj F) d)) ⟦2 * (d : ℤ)⟧ ⟶
            𝟙_ (DScalar.{u} ell))
      (B : Pairings ell
        ((sections ell (D.geometricFiber X₀).hom).obj ((DerivedCategory.singleFunctor _ 0).obj F))
        ((sections ell (D.geometricFiber X₀).hom).obj
          (twistedDual ell ((DerivedCategory.singleFunctor _ 0).obj F) d)) d),
      IsScalarNormalizedPairing ell D.k _ _ d
        (fibrePairing D ell hEll (D.geometricFiber X₀) d
          ((DerivedCategory.singleFunctor _ 0).obj F)
          (twistedDual ell ((DerivedCategory.singleFunctor _ 0).obj F) d)
          (evaluation ell ((DerivedCategory.singleFunctor _ 0).obj F) d)) b ∧
      IsIso (curry b) ∧ IsInducedPairing ell _ _ d b B ∧
      (∀ i : ℤ,
        FiniteDimensional (Scalar.{u} ell)
          ((DerivedCategory.homologyFunctor (V.{u} ell) i).obj
            ((sections ell (D.geometricFiber X₀).hom).obj
              ((DerivedCategory.singleFunctor _ 0).obj F))) ∧
        FiniteDimensional (Scalar.{u} ell)
          ((DerivedCategory.homologyFunctor (V.{u} ell) (2 * (d : ℤ) - i)).obj
            ((sections ell (D.geometricFiber X₀).hom).obj
              (twistedDual ell ((DerivedCategory.singleFunctor _ 0).obj F) d))) ∧
        Function.Bijective (B i) ∧ Function.Bijective (B i).flip) ∧
      ∀ (i : ℤ) (x : (DerivedCategory.homologyFunctor (V.{u} ell) i).obj
        ((sections ell (D.geometricFiber X₀).hom).obj ((DerivedCategory.singleFunctor _ 0).obj F)))
        (y : (DerivedCategory.homologyFunctor (V.{u} ell) (2 * (d : ℤ) - i)).obj
          ((sections ell (D.geometricFiber X₀).hom).obj
            (twistedDual ell ((DerivedCategory.singleFunctor _ 0).obj F) d))),
        B i ((cohomologyFrobenius D ell X₀ ((DerivedCategory.singleFunctor _ 0).obj F)
            phi i).hom x)
          ((cohomologyFrobenius D ell X₀
            (twistedDual ell ((DerivedCategory.singleFunctor _ 0).obj F) d)
            (twistedPhi D ell hEll X₀ ((DerivedCategory.singleFunctor _ 0).obj F) phi d)
            (2 * (d : ℤ) - i)).hom y) = B i x y := by
  sorry

end WeilConjectures.DisconnectedFibrePoincare
