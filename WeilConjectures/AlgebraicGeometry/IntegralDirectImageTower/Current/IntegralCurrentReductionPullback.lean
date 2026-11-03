/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.Current.IntegralCurrentOrdinaryPullback
import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.SequenceComparisonConstruction.NormalizedDerivedComparisonDescent
import WeilConjectures.CategoryTheory.Derived.DerivedResolvingPairRestriction
import WeilConjectures.CategoryTheory.SixFunctors.UnaryWhiskeringOfProduct
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Unique normalized scalar/pullback comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem scalar_geometric_hom_ext (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules l E Y) (n : ℕ)
    (N : Scheme.proEtaleRingModules X (SpTowerShriek.B l E X n))
    (a b : (ordinaryLevel l E s X n).obj
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) ⟶ N)
    (h : ∀ (V : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x)) =
      b.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x))) : a = b := by
  let A := (s.towers X).scalar
    (spIntegralReductionScalar l E X (s.reduction X).coefficient n)
  apply (A.ordinaryAdj.homEquiv _ N).injective
  apply geometric_hom_ext l E f M
  intro V x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change a.val.app _ ((A.ordinaryAdj.unit.app _).val.app _ _) =
    b.val.app _ ((A.ordinaryAdj.unit.app _).val.app _ _)
  rw [A.unit_normalized]
  exact h V x

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem reductionPull_ordinary_ext (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p q : ScalarPull l E s e f) :
    p.ordinary = q.ordinary := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have he (n : ℕ) : ordinaryPullLevelMap l E s e f p.ordinary M n =
      ordinaryPullLevelMap l E s e f q.ordinary M n := by
    apply scalar_geometric_hom_ext l E s f M n
    intro V x
    exact (p.generators M n V x).trans (q.generators M n V x).symm
  have hl (n : ℕ) :
      (SpTowerShriek.ev l E X n).map (p.ordinary.hom.app M) =
        (SpTowerShriek.ev l E X n).map (q.ordinary.hom.app M) := by
    apply (cancel_epi ((ordinaryReductionEvaluation l E s e X n).inv.app _)).1
    apply (cancel_mono (((s.operations.geometry f).ordinaryPullEvaluation n).hom.app
      ((ordinaryReduction l E s Y).obj M) ≫
      (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).map
        ((ordinaryReductionEvaluation l E s e Y n).hom.app M))).1
    simpa only [ordinaryPullLevelMap, Category.assoc] using he n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rcases U with ⟨n, V⟩
  ext x
  have h := congrArg (fun a ↦ a.val.app (op V) x) (hl n)
  exact h

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem reductionPull_derived_ext (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p q : ScalarPull l E s e f)
    (ho : p.ordinary = q.ordinary) : p.derived = q.derived := by
  apply Iso.ext
  apply internal_resolving_ext l E _ _
  intro P hP hf
  have := reduction_comparison_isIso l E s Y P hP
  apply (cancel_mono
    ((SpTowerShriek.pull l E s.base (s.operations.geometry f)).map
        (reductionComplexComparison l E s Y P) ≫
      (s.operations.geometry f).pull.mapDerivedCategoryFactors.hom.app
        (((ordinaryReduction l E s Y).mapHomologicalComplex (.up ℤ)).obj P))).1
  rw [p.representatives P hP hf, q.representatives P hP hf, ho]

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem reductionPull_ext (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p q : ScalarPull l E s e f)
    (ho : p.ordinary = q.ordinary) (hd : p.derived = q.derived) : p = q := by
  cases p
  cases q
  dsimp only at ho hd
  cases ho
  cases hd
  rfl

/-- The scalar/pullback comparison is fixed uniquely by its tensor generators and
flat-term K-flat representative equation. Source: blueprint integral direct-image
proof paragraphs (2)--(3), scalar compatibility before the open and proper mates.
Proof: put r = s.base.ramification and k = r(n+1)-1. The index r is positive.
The ideal equality identifies the actual ell-power quotient with the uniformizer
quotient at k+1 = r(n+1). Its projection is continuous by the uniformizer coset basis.
Apply finite discrete encoding to its continuous condensed coefficient ring.
On profinite-test sections the integral coefficient comparison sends a continuous
section to its actual quotient sections. The fixed completed projection has the
same composite with integralConstantToCompletion. Finite-quotient hom
extensionality therefore identifies this map with spIntegralReductionScalar,
using coefficient_normalized. This gives the actual scalar/inverse-image square.
The scalar and geometric adjunctions identify the two ordinary composites: both
units send x to one tensor unit_f(x). The internal/section equivalence preserves
these units. Quotient transitions commute because reduction sends one to one;
check the resulting equality on inverse-image and tensor generators and then
sheafify. Transport this strict isomorphism through the sectionwise realizations.
The given evaluation e is the identity on sections, so its generator equation is
exactly the required one. Resolve a complex by a flat-term K-flat section complex.
Exact monoidal inverse image preserves its flat terms and K-flatness. Both fixed
reduction counits compute such models. Conjugating the ordinary comparison by
those counits and pullComplexComparison gives an invertible map on models;
localization extends it uniquely to the derived comparison. Its construction is
precisely the representatives equation. Finally the ordinary generator formula
forces every ordinary component by local generation. The representative equation
forces each derived component on a resolving model by cancellation; naturality
then forces it on every object. Equality of the two isomorphisms and proof
irrelevance give uniqueness of the full record. Thus choosing this record does
not choose arbitrary data from a bare existence statement. No invertibility of
ell, boundedness, or flatness of a quotient is used. Empty schemes, zero modules,
identity maps and the first positive quotient satisfy the same formulas.
(blueprint: lem-sp-current-reduction-pullback). -/
theorem normalized_reduction_pullback_existsUnique (s : Coefficients l E)
    (e : Evaluation l E s) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! _p : ScalarPull l E s e f, True := by
  obtain ⟨q, hq⟩ := ordinary_reduction_pullback_exists l E s e f
  obtain ⟨d, hd, _⟩ := derived_reduction_pullback_existsUnique l E s f q
  let p : ScalarPull l E s e f := ⟨q, hq, d, hd⟩
  refine ⟨p, trivial, ?_⟩
  intro p' _
  have ho := reductionPull_ordinary_ext l E s e f p' p
  have hd := reductionPull_derived_ext l E s e f p' p ho
  exact reductionPull_ext l E s e f p' p ho hd

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
