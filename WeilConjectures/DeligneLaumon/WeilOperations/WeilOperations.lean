/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeWeilDerivedFramework
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.CategoryTheory.Endofunctor.EquivalenceOrbitInduction
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.ProEtaleCoefficients.DerivedMonoidalClosed
public import WeilConjectures.DeligneLaumon.CondensedWeilProjection.CondensedWeilProjectionComparisonData
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.BifunctorHomComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCompIso
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.AlgebraicGeometry.Exact.ExactCondensedExchangeComparison
public import WeilConjectures.CategoryTheory.AdjunctionUnitCounitNormalization
public import WeilConjectures.CategoryTheory.Endofunctor.FixedPairDerivedSingleStructure
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusCompactExchangeInvertible
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
public import WeilConjectures.SmoothPurity.CurrentExceptionalAdjointAdmissibility
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.Endofunctor.FixedPairRestrictedAdjunction
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical Weil structures on operations and their algebraic maps

Source: current blueprint, unit lem-fix-weil-operations, full statement and
corresponding proof paragraphs 1--3 (blueprint: lem-fix-weil-operations).

The comparison equations below identify the maps after `nativeWeilDerivedForget`.
In particular an arbitrary morphism or an arbitrary isomorphism does not satisfy this
interface. Constructible restrictions are conditional on the underlying preservation
properties; exceptional inverse image is conditional on the supplied admissible adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace WeilConjectures
namespace WeilOperations

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)

/-- The actual continuous inclusion of integral scalars into the chosen condensed ring.
Source: coefficient twists, scalar extension of the root line
(blueprint: lem-fix-weil-operations). -/
def integralCoefficientMap :
    Profinite.continuousMapRingObj.{u} ℤ_[ell] ⟶ WeilCoefficient.ab c :=
  match c with
  | .finite E => (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.padicIntCondensedRingToPadicCondensedRing ell ≫
          Profinite.padicCondensedRingToPadicSubfieldCondensedRing ell E)
  | .qbar => Profinite.padicIntRingObjToPadicAlgCl ell

/-- The scalar map preserves multiplication and the unit because it comes from a ring
map. Source: coefficient twists, scalar extension (blueprint: lem-fix-weil-operations). -/
instance integralCoefficientMap_isMonHom : IsMonHom (integralCoefficientMap ell c) := by
  cases c <;> dsimp [integralCoefficientMap] <;> infer_instance

attribute [-instance] CondensedRing.ProjectionMorphismData.category in
/-- The coefficient's actual root line, formed by scalar extension of the inverse limit
of roots. Source: def-coefficient-twists-detailed, rational and Qbar paragraphs, used in
paragraph 3 of lem-fix-weil-operations.proof.md (blueprint: lem-fix-weil-operations). -/
def twistOne (X : Scheme.{u}) : nativeWeilModuleCategory ell c X := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact (Mod.extendScalars (coefficientMap (integralCoefficientMap.{u} ell c) X)).obj
    (tateModule X ell)

/-- The actual signed coefficient twist; its zero and negative powers are those of the
recorded coefficient construction. Source: def-coefficient-twists-detailed, final display,
used in paragraph 3 of lem-fix-weil-operations.proof.md
(blueprint: lem-fix-weil-operations). -/
def ordinaryTwist (X : Scheme.{u}) (m : ℤ) :=
  coefficientTwistFunctor X (condensedRingObj (WeilCoefficient.ab c) X)
    (twistOne ell c X) m

/-- Specialize the existing root-coordinate coefficient presentation to the two
coefficients of this node. Source: prescribed coefficient twists, paragraph 3 of
lem-fix-weil-operations.proof.md (blueprint: lem-fix-weil-operations). -/
def coefficientPresentation : PurityTransport.Coefficient ell :=
  match c with
  | .finite E => .rational E
  | .qbar => .closure

variable {D ell c} (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The normalized comparison on objects, through actual derived forgetting.
Source: lem-fix-weil-operations.proof.md, paragraph 2 (blueprint: lem-fix-weil-operations). -/
def TensorModel.tensorIso (t : TensorModel (D := D) (ell := ell) (c := c) X₀)
    (K L : nativeWeilDerivedPairCategory D ell c X₀) :
    (nativeWeilDerivedForget D ell c X₀).obj
      (((nativeDerivedTensor D ell c X₀).obj K).obj L) ≅
    ((nativeWeilDerivedForget D ell c X₀).obj K ⊗
      (nativeWeilDerivedForget D ell c X₀).obj L) := by
  letI := t.presentation
  exact eqToIso (congrArg (fun F ↦ (nativeWeilDerivedForget D ell c X₀).obj
    ((F.obj K).obj L)) t.tensor_is_native.symm) ≪≫
      (t.comparison.derived.app K).app L

variable {X₀} {Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Geometric compactification with the same middle finite-field model used by the
native compact-support functor. Source: lem-fix-weil-operations.proof.md, paragraph 1,
compactification comparisons (blueprint: lem-fix-weil-operations). -/
def geometricCompactification (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left) :
    Compactification (D.geometricFiberMap f₀) where
  Z := (D.geometricFiber (nativeWeilCompactificationModel D f₀ c₀)).left
  i := D.geometricFiberMap (nativeWeilCompactificationOpen D f₀ c₀)
  g := D.geometricFiberMap (nativeWeilCompactificationProper D f₀ c₀)
  comm := by
    let j := nativeWeilCompactificationOpen D f₀ c₀
    let p := nativeWeilCompactificationProper D f₀ c₀
    have h : f₀ = j ≫ p := Over.OverMorphism.ext c₀.comm
    exact (congrArg (fun h ↦ D.geometricFiberMap h) h).trans
      (congrArg Over.Hom.left
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map_comp j p))
  isProper := MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      (nativeWeilCompactificationProper D f₀ c₀) inferInstance
  isOpenImmersion := nativeWeilGeometricOpen D
    (nativeWeilCompactificationOpen D f₀ c₀)

/-- Ordinary adjunction with the unique derived-unit-normalized forgetting comparison.
The canonical Ex_* is the mate of pullback square composition; the unit and counit are
fixed by the ordinary adjunction, not selected independently.
Source: lem-fix-weil-operations.proof.md, paragraph 3, ordinary adjunction
(blueprint: lem-fix-weil-operations). -/
structure OrdinaryModel (f₀ : X₀ ⟶ Y₀)
    (tX : TensorModel (D := D) (ell := ell) (c := c) X₀)
    (tY : TensorModel (D := D) (ell := ell) (c := c) Y₀) where
  comparison : CondensedWeilProjection.ComparisonData (WeilCoefficient.ab c)
    (D.geometricFrobenius X₀) (D.geometricFrobenius Y₀)
    (D.geometricFiberMap f₀) (nativeWeilGeometricSquare D f₀)
    (tZ := tX.presentation) (tY := tY.presentation)
  unit_normalization :
    letI := tX.presentation
    letI := tY.presentation
    ∀ K : nativeWeilDerivedPairCategory D ell c Y₀,
    (nativeWeilDerivedForget D ell c Y₀).map (comparison.adjunction.unit.app K) =
      (CondensedRing.derivedUpperStarLowerStarAdjunction (WeilCoefficient.ab c)
        (D.geometricFiberMap f₀)).unit.app ((nativeWeilDerivedForget D ell c Y₀).obj K) ≫
      (CondensedRing.moduleObjectDerivedPushforward (WeilCoefficient.ab c)
        (D.geometricFiberMap f₀)).map (comparison.pullForget.inv.app K) ≫
      comparison.pushForget.inv.app ((nativeWeilPullback D ell c f₀).obj K)

/-- The ordinary-operation model needs no separate unit compatibility input: the
normalized counit already determines it.

Source: lem-fix-weil-operations.proof.md, paragraph 3, ordinary adjunction
(blueprint: lem-fix-weil-operations). -/
def OrdinaryModel.ofComparisonData (f₀ : X₀ ⟶ Y₀)
    (tX : TensorModel (D := D) (ell := ell) (c := c) X₀)
    (tY : TensorModel (D := D) (ell := ell) (c := c) Y₀)
    (d : CondensedWeilProjection.ComparisonData (WeilCoefficient.ab c)
      (D.geometricFrobenius X₀) (D.geometricFrobenius Y₀)
      (D.geometricFiberMap f₀) (nativeWeilGeometricSquare D f₀)
      (tZ := tX.presentation) (tY := tY.presentation)) : OrdinaryModel f₀ tX tY where
  comparison := d
  unit_normalization := by
    let := tX.presentation
    let := tY.presentation
    intro K
    exact adjunction_unit_of_counit_normalization d.adjunction
      (CondensedRing.derivedUpperStarLowerStarAdjunction (WeilCoefficient.ab c)
        (D.geometricFiberMap f₀)) d.pullForget d.pushForget d.counit_normalization K

/-- Native Frobenius after the canonical exact/left-derived comparison.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-fix-weil-operations). -/
def structureIso (K : nativeWeilDerivedPairCategory D ell c X₀) :=
  (CondensedRing.modulePullbackExactComparison (WeilCoefficient.ab c)
    (D.geometricFrobenius X₀).hom).app ((nativeWeilDerivedForget D ell c X₀).obj K) ≪≫
      (nativeWeilDerivedStructure D ell c X₀).app K

/-- The fixed direct-image exchange of the Frobenius square: the Ex_* mate.
Source: lem-fix-weil-operations.proof.md, paragraph 1
(blueprint: lem-fix-weil-operations). -/
def directFrobenius (f₀ : X₀ ⟶ Y₀) :=
  CondensedRing.moduleObjectDerivedExchange (WeilCoefficient.ab c)
    (nativeWeilGeometricSquare D f₀)

/-- Frobenius exchange for compact support is invertible. The direct exchange is
invertible for the proper factor because both vertical arrows are isomorphisms; the
open factor is a composite of whiskered isomorphisms. No constructibility assumption
is required for this calculation.
Source: lem-fix-weil-operations.proof.md, paragraph 1, inverse-square argument
(blueprint: lem-fix-weil-operations). -/
theorem compactFrobenius_isIso (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left) :
    IsIso (compactFrobenius (D := D) (c := c) f₀ c₀) := by
  exact FrobeniusSquareExchange.compact_isIso _ _ _ _

/-- Compact support on pairs in the underlying condensed derived category. The
Frobenius comparison is the specified Ex_! transported through the exact comparison.
Source: lem-fix-weil-operations.proof.md, automorphism-square paragraph
(blueprint: lem-sf-condensed-pair-exceptional-adjunction). -/
def pairCompactComparison (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left) :
    CondensedRing.rightDerivedLowerShriekOfCompactification (WeilCoefficient.ab c)
        (geometricCompactification (D := D) f₀ c₀) ⋙
      (CondensedRing.upperStar (WeilCoefficient.ab c)
        (D.geometricFrobenius Y₀).hom).mapDerivedCategory ≅
    (CondensedRing.upperStar (WeilCoefficient.ab c)
        (D.geometricFrobenius X₀).hom).mapDerivedCategory ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification (WeilCoefficient.ab c)
        (geometricCompactification (D := D) f₀ c₀) := by
  letI := compactFrobenius_isIso (D := D) (c := c) f₀ c₀
  let F := CondensedRing.rightDerivedLowerShriekOfCompactification (WeilCoefficient.ab c)
    (geometricCompactification (D := D) f₀ c₀)
  exact Functor.isoWhiskerLeft F
      (CondensedRing.modulePullbackExactComparison (WeilCoefficient.ab c)
        (D.geometricFrobenius Y₀).hom).symm ≪≫
    asIso (compactFrobenius (D := D) (c := c) f₀ c₀) ≪≫
    Functor.isoWhiskerRight
      (CondensedRing.modulePullbackExactComparison (WeilCoefficient.ab c)
        (D.geometricFrobenius X₀).hom) F

/-- The exceptional Frobenius mate uses exactly the inverse Ex_! mate after
transporting between total and exact derived Frobenius.
Source: lem-fix-weil-operations.proof.md, exceptional-adjoint paragraph
(blueprint: lem-sf-condensed-pair-exceptional-adjunction).

Proof: apply the mate-transport identity to the specified compact exchange and
the two canonical exact/total comparisons. Naturality of the unit and counit gives
the two displayed boundary comparisons, with no change to the intervening mate. -/
theorem pairExceptionalMate_normalization (f₀ : X₀ ⟶ Y₀)
    (c₀ : Compactification f₀.left)
    (G : nativeWeilDerivedCategory ell c (D.geometricFiber Y₀).left ⥤
      nativeWeilDerivedCategory ell c (D.geometricFiber X₀).left)
    (a : CondensedRing.rightDerivedLowerShriekOfCompactification (WeilCoefficient.ab c)
      (geometricCompactification (D := D) f₀ c₀) ⊣ G)
    (N : nativeWeilDerivedCategory ell c (D.geometricFiber Y₀).left) :
    let := compactFrobenius_isIso (D := D) (c := c) f₀ c₀
    (mateEquiv a a (TwoSquare.mk _ _ _ _
      (pairCompactComparison (D := D) (c := c) f₀ c₀).inv)).natTrans.app N =
      (CondensedRing.modulePullbackExactComparison (WeilCoefficient.ab c)
        (D.geometricFrobenius X₀).hom).inv.app (G.obj N) ≫
      (mateEquiv a a (TwoSquare.mk _ _ _ _
        (asIso (compactFrobenius (D := D) (c := c) f₀ c₀)).inv)).natTrans.app N ≫
      G.map ((CondensedRing.modulePullbackExactComparison (WeilCoefficient.ab c)
        (D.geometricFrobenius Y₀).hom).hom.app N) := by
  let := compactFrobenius_isIso (D := D) (c := c) f₀ c₀
  exact Endofunctor.IsoAlgebra.mateComparison_transport a
    (asIso (compactFrobenius (D := D) (c := c) f₀ c₀))
    (CondensedRing.modulePullbackExactComparison (WeilCoefficient.ab c)
      (D.geometricFrobenius X₀).hom)
    (CondensedRing.modulePullbackExactComparison (WeilCoefficient.ab c)
      (D.geometricFrobenius Y₀).hom) N

/-- Canonical forgetting of compact support, assembled from exact open forgetting and
unit-normalized proper forgetting in the displayed order. Source:
lem-fix-weil-operations.proof.md, paragraph 1 (blueprint: lem-fix-weil-operations). -/
def compactForget (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left)
    (tZ : TensorModel (D := D) (ell := ell) (c := c)
      (nativeWeilCompactificationModel D f₀ c₀))
    (tY : TensorModel (D := D) (ell := ell) (c := c) Y₀)
    (d : OrdinaryModel (nativeWeilCompactificationProper D f₀ c₀) tZ tY) :
    nativeWeilCompactSupport D ell c f₀ c₀ ⋙ nativeWeilDerivedForget D ell c Y₀ ≅
      nativeWeilDerivedForget D ell c X₀ ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification (WeilCoefficient.ab c)
          (geometricCompactification (D := D) f₀ c₀) := by
  letI := tZ.presentation
  letI := tY.presentation
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ d.comparison.pushForget ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (nativeWeilOpenExtensionForget (WeilCoefficient.ab c)
        (D.geometricFrobenius X₀)
        (D.geometricFrobenius (nativeWeilCompactificationModel D f₀ c₀))
        (D.geometricFiberMap (nativeWeilCompactificationOpen D f₀ c₀))
        (nativeWeilGeometricSquare D (nativeWeilCompactificationOpen D f₀ c₀))) _ ≪≫
    Functor.associator _ _ _

/-- Open restriction commutes with direct image for this Cartesian open square.
Source: lem-fix-weil-operations.proof.md, paragraph 3, composition comparison;
compactification-triangle construction of R(fg)_! (blueprint: lem-fix-weil-operations).
Proof plan: compute restriction on the pulled-back open on sheaves, where it is the
identity. Open extension is exact, so restriction preserves K-injectives by its
adjunction. Derive that identity and identify the comparison with its unit-square-counit
mate. Its inverse is the derived restriction identity in the opposite direction. -/
theorem triangleExchange_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    IsIso (CondensedRing.moduleObjectDerivedExchange Λ T.isPullback.flip.toCommSq) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  obtain ⟨e⟩ := totalDerivedExchange_exact_comparisonFor Λ T.isPullback.flip.toCommSq K
  have hi := (CondensedRing.derivedOpenRestrictionNormalization Λ T.isPullback.flip).derived_isIso
  have h : exactCondensedExchangeFor Λ T.isPullback.flip.toCommSq =
      CondensedRing.derivedDirectImageOpenRestriction Λ T.isPullback.flip.toCommSq := by
    unfold exactCondensedExchangeFor CondensedRing.derivedDirectImageOpenRestriction
      CondensedRing.derivedOpenCoherencePullbackSquare condensedPullbackSquareFor
      CondensedRing.openCoherencePullbackSquare
    rfl
  have : IsIso ((exactCondensedExchangeFor Λ T.isPullback.flip.toCommSq).app K) := by
    rw [h]
    infer_instance
  exact (Arrow.isIso_iff_isIso_of_isIso e.hom).mpr this

/-- The canonical compact-support compositor on a triangle: transpose the inverse
restriction exchange, compose the two opens, then compose the proper direct images.
No arbitrary interchange map is chosen.
Source: lem-fix-weil-operations.proof.md, paragraph 3, compositor/pasting sentence;
compactification-triangle construction of R(fg)_! (blueprint: lem-fix-weil-operations). -/
def triangleComposition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ T.cf ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification Λ T.cg).obj K) ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ T.cfg).obj K := by
  letI := triangleExchange_isIso Λ T
  let δ := ((mateEquiv (CondensedRing.CompactificationReindexing.oa Λ T.q)
    (CondensedRing.CompactificationReindexing.oa Λ T.cg.i)).symm
      (TwoSquare.mk _ _ _ _
        (asIso (CondensedRing.moduleObjectDerivedExchange Λ
          T.isPullback.flip.toCommSq)).inv)).natTrans
  let e := CondensedRing.CompactificationReindexing.jComp Λ T.cf.i T.q ≪≫
    CondensedRing.CompactificationReindexing.jCongr Λ T.i_q
  exact (CondensedRing.moduleObjectDerivedPushforward Λ T.cg.g).map
      (δ.app ((CondensedRing.CompactificationReindexing.J Λ T.cf.i).obj K) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ T.p).map (e.hom.app K)) ≫
    (CondensedRing.rightDerivedLowerStarComp Λ T.p T.cg.g).hom.app
      ((CondensedRing.CompactificationReindexing.J Λ T.cfg.i).obj K) ≫
    (eqToIso (congrArg (CondensedRing.moduleObjectDerivedPushforward Λ) T.p_g)).hom.app
      ((CondensedRing.CompactificationReindexing.J Λ T.cfg.i).obj K)

end WeilOperations

open WeilOperations

set_option maxHeartbeats 1600000 in
-- Elaborate the native derived endpoints and their dependent comparisons.
end WeilConjectures
