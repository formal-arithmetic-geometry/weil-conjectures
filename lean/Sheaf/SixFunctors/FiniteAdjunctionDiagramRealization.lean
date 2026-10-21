/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.SixFunctors.FiniteAdjunctionSystemData
public import Sheaf.SixFunctors.IntegralDualizing
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

import Sheaf.Paper.SemilinearDerivedSections
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Paper.CoefficientSystemDerivedComparison
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.SystemLevelLeftExtension
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts
import Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.UnboundedSiteComparison
import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.SixFunctors.FiniteExceptional
import Sheaf.Paper.SfPreservationClass
import Sheaf.Paper.NormalizedDVRTower
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.SixFunctors.FiniteDualizing
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.WeilVerdierPreservationStrata
import Sheaf.SixFunctors.FiniteCoefficientVerdier
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
import Sheaf.SmoothPurity.InternalAdjunctionEvaluation
import Sheaf.Paper.FiniteStageVerdierBiduality
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Finite exceptional operations and enriched adjunction on systems

Source: current blueprint main-20261015, finite exceptional lemma and
prop-coef-integral-exceptional-adjoint, proof paragraphs 1--2; Stacks 06YS, 0A95,
0941 and 079P (blueprint: lem-coef-finite-adjunction-diagram-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
variable {l E D hl f c}

/-- The actual regular module over the sequence ring.
Source: node proof step 9 (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def ordinaryCoefficientUnit (W : Scheme.{u}) : coefficientSequenceModules l E W :=
  SheafOfModules.unit ((sheafCompose
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (coefficientSequenceCommRingSheaf l E W))

/-- The coefficient-unit system is the actual sequence ring as a module in degree zero.
Source: node proof step 9 (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def coefficientUnit (W : Scheme.{u}) : coefficientSequenceDerived l E W :=
  (DerivedCategory.singleFunctor (coefficientSequenceModules l E W) 0).obj
    (ordinaryCoefficientUnit W)

/-- The coefficient unit is normalized and finite free at every finite level.
Source: Stacks 06YY; node proof step 9
(blueprint: lem-coef-finite-adjunction-diagram-realization).
Proof: exact evaluation gives the quotient coefficient unit in degree zero.
Each quotient tensor sends the free rank-one module to the free rank-one module,
and its transition adjunct is the identity. Thus normalization holds, each level
is constructible with Tor interval [0,0], and the unit belongs to the full domain. -/
theorem coefficientUnit_mem (W : Scheme.{u}) :
    domain l E W (coefficientUnit (l := l) (E := E) W) := by
  sorry

/-- The normalized coefficient unit, with its unchanged object and maps.
Source: node proof step 9 (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def normalizedUnit (W : Scheme.{u}) : (domain l E W).FullSubcategory :=
  ⟨coefficientUnit W, coefficientUnit_mem W⟩

/-- System Verdier dual, using the recorded system internal Hom, without a new copy.
Source: node proof steps 9--11
(blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def dual (W : Scheme.{u}) (Ω : coefficientSequenceDerived l E W) :
    (coefficientSequenceDerived l E W)ᵒᵖ ⥤ coefficientSequenceDerived l E W :=
  (Functor.curry.obj (coefficientSequenceInternalHom l E W)).flip.obj Ω

/-- The double-dual pullback formula, as an actual functor before any evaluation.
Source: node proof step 11 (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def dualFormula (ΩX : coefficientSequenceDerived l E X)
    (ΩY : coefficientSequenceDerived l E Y) :
    coefficientSequenceDerived l E Y ⥤ coefficientSequenceDerived l E X :=
  (dual Y ΩY).rightOp ⋙ (integralComparisonDerivedSequencePullback l E f).op ⋙ dual X ΩX

/-- Source of the enriched adjunction as an actual bifunctor on the normalized categories.
Source: node proof step 15 (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def Realization.mappingSource
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (r : Realization l E D hl f c SX SZ SY) :=
  (r.F ⋙ (domain l E Y).ι).op.prod (domain l E Y).ι ⋙ coefficientSequenceGlobalHom l E Y

/-- Target of the same enriched adjunction, retaining all system transitions.
Source: node proof step 15 (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def Realization.mappingTarget
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (r : Realization l E D hl f c SX SZ SY) :=
  (domain l E X).ι.op.prod (r.G ⋙ (domain l E X).ι) ⋙ coefficientSequenceGlobalHom l E X

/-- The finite global mapping source uses exactly the recorded finite compact support.
Source: node final display (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def finiteMappingSource (n : ℕ) :
    (FiniteExceptional.domain l E X n).FullSubcategoryᵒᵖ ×
      (FiniteExceptional.domain l E Y n).FullSubcategory ⥤
        DerivedCategory AddCommGrpCat.{u+1} :=
  (FiniteExceptional.F l E D hl f c n ⋙ (FiniteExceptional.domain l E Y n).ι).op.prod
    (FiniteExceptional.domain l E Y n).ι ⋙ coefficientFiniteGlobalHom.{u, u} l E Y n

/-- The finite global mapping target uses exactly the recorded finite exceptional functor.
Source: node final display (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def finiteMappingTarget (n : ℕ) :
    (FiniteExceptional.domain l E X n).FullSubcategoryᵒᵖ ×
      (FiniteExceptional.domain l E Y n).FullSubcategory ⥤
        DerivedCategory AddCommGrpCat.{u+1} :=
  (FiniteExceptional.domain l E X n).ι.op.prod
    (FiniteExceptional.G l E D hl f c n ⋙ (FiniteExceptional.domain l E X n).ι) ⋙
      coefficientFiniteGlobalHom.{u, u} l E X n

/-- Enriched realization: the actual system transpose is invertible, and the natural
isomorphism is derived sections of its inverse. The finite comparison includes the
same finite adjunction, its Hom action, and every finite evaluation square.
Source: node proof steps 15--17
(blueprint: lem-coef-finite-adjunction-diagram-realization). -/
structure Enriched
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (r : Realization l E D hl f c SX SZ SY)
    (g : Geometry l E f SX SY) (s : SectionsPush g)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal) where
  internalIsIso : ∀ M N, IsIso (r.enrichedMap g βX βY M N)
  iso : r.mappingSource ≅ r.mappingTarget
  component : ∀ M N, iso.hom.app (op M, N) =
    r.globalMap g s βX βY M N (internalIsIso M N)
  finiteIso : ∀ n : ℕ,
    finiteMappingSource (l := l) (E := E) (D := D) (hl := hl) (f := f) (c := c) n ≅
      finiteMappingTarget (l := l) (E := E) (D := D) (hl := hl) (f := f) (c := c) n
  finiteHom : ∀ (n : ℕ) (M : (FiniteExceptional.domain l E X n).FullSubcategory)
    (N : (FiniteExceptional.domain l E Y n).FullSubcategory)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).obj
      ((finiteMappingSource (l := l) (E := E) (D := D) (hl := hl)
        (f := f) (c := c) n).obj (op M, N))),
    coefficientFiniteHomEquiv l E X n M.obj ((FiniteExceptional.G l E D hl f c n).obj N).obj
        (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
          ((finiteIso n).hom.app (op M, N))) x) =
      ((FiniteExceptional.adjunction l E D hl f c n).homEquiv M N
        (ObjectProperty.homMk
          (coefficientFiniteHomEquiv l E Y n
            ((FiniteExceptional.F l E D hl f c n).obj M).obj N.obj x))).hom
  finiteEvaluation : ∀ (n : ℕ) (M : (domain l E X).FullSubcategory)
    (N : (domain l E Y).FullSubcategory),
    (coefficientMappingEvaluation.{u+1} n).map (iso.hom.app (op M, N)) ≫
      (SX.globalEvaluation M.obj (r.G.obj N).obj M.property.1 (r.G.obj N).property.1 n).hom ≫
      (coefficientFiniteGlobalHom.{u, u} l E X n).map (Prod.mkHom (𝟙 _)
        (((r.exceptionalEvaluation n).hom.app N).hom)) =
    (SY.globalEvaluation (r.F.obj M).obj N.obj (r.F.obj M).property.1 N.property.1 n).hom ≫
      (coefficientFiniteGlobalHom.{u, u} l E Y n).map
        (Prod.mkHom (((r.supportEvaluation n).inv.app M).hom.op) (𝟙 _)) ≫
      (finiteIso n).hom.app ((evaluation l E X n).op.prod (evaluation l E Y n) |>.obj (op M, N))

/-- A normalized dualizing system presents precisely the prescribed finite dualizing
tower and its total derived limit, with the SAME finite projections. In particular this
predicate makes no assertion about exceptional inverse image on integral inputs.
Source: node proof step 9 and prop-coef-integral-dualizing
(blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def DualizingSpec (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))] (Ω : (domain l E W).FullSubcategory) : Prop :=
  letI : HasCountableProducts (completedIntegralDerivedCategory l E W D hl) :=
    integralOperationsDerivedCountableProducts l E W
  ∃ (T : NormalizedDVRTower l E W D hl)
    (e : ∀ n : ℕ, T.M n ≅ (coefficientSequenceDerivedEvaluation l E W n).obj Ω.obj)
    (ω : ∀ n : ℕ, (coefficientSequenceDerivedEvaluation l E W n).obj Ω.obj ≅
      integralDualizingFiniteTerm l E D W n)
    (t : T.tower ≅ (coefficientSequenceDerivedRestriction l E W).obj Ω.obj)
    (p : (coefficientSequenceLimit l E W).obj Ω.obj ⟶
      ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower) ⟶
      ((coefficientSequenceLimit l E W).obj Ω.obj)⟦(1 : ℤ)⟧),
    (∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E W h).map (e n).hom =
        (e m).hom ≫ (coefficientSequenceDerivedTransition l E W h).app Ω.obj) ∧
    (∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition l E W h).app Ω.obj ≫
        (normalizedDVRRes l E W h).map (ω n).hom =
      (ω m).hom ≫
        (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E W h)).homEquiv _ _
          (integralDualizingFiniteComparison l E D W hl h)) ∧
    (∀ n : ℕ, (normalizedDVRTowerEvaluation l E W D hl n).map t.hom ≫
        (coefficientRestrictedEvaluationIso l E W n).hom.app Ω.obj =
      (T.evaluationIso n).hom ≫ (coefficientFiniteDerivedRestriction l E W n).map (e n).hom) ∧
    IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E W D hl n.le_succ).app T.tower)
      ((coefficientSequenceLimit l E W).obj Ω.obj) p δ ∧
    (∀ n : ℕ, p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom ≫
        (coefficientFiniteDerivedRestriction l E W n).map (e n).hom =
      (coefficientSequenceProjection l E W n).app Ω.obj) ∧
    IntegralDualizingLimitPresentation l E D hl W T
      ((coefficientSequenceLimit l E W).obj Ω.obj) ∧
    Nonempty ((coefficientSequenceLimit l E W).obj Ω.obj ≅
      (integralDualizingLimit l E W).obj T.tower)

/-- A structure morphism commutes with the identity structure morphism on its base.
Source: the definition of a scheme over a base
(blueprint: lem-coef-finite-adjunction-diagram-realization).
Proof: the required equation is a_W composed with the identity equals a_W,
which is the category right identity law. -/
theorem structure_isOver (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    (W ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := by
  sorry

/-- The canonical over-base structure on the structure morphism.
Source: the structure-map identity
(blueprint: lem-coef-finite-adjunction-diagram-realization). -/
instance structureOver (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    (W ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := structure_isOver W

/-- The structure-map instance of the SAME finite-operation realization. Its dualizing
system is literally its exceptional functor applied to the coefficient unit.
Source: node proof step 9 (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
structure DualizingOperation (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (SW : CoefficientDerivedSystemCalculus l E W)
    (SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))) where
  /-- Regular module evaluation is fixed on all sections before exact localization. -/
  unitEvaluation : ∀ n : ℕ,
    (coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj
        (ordinaryCoefficientUnit (Spec (.of D.k))) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) n)
  unitEvaluation_sections : ∀ (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj
      (ordinaryCoefficientUnit (Spec (.of D.k)))).val.obj U),
    HEq ((unitEvaluation n).hom.val.app U x) x
  intermediate : CoefficientDerivedSystemCalculus l E (integralDualizingCompactification D W).Z
  realization : Realization l E D hl (W ↘ Spec (.of D.k))
    (integralDualizingCompactification D W) SW intermediate SS
  dualizing : DualizingSpec (D := D) (hl := hl) W
    (realization.G.obj (normalizedUnit (Spec (.of D.k))))

/-- The absolute dualizing system, with no arbitrary choice of its finite terms.
Source: node proof step 9 (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def DualizingOperation.omega {W : Scheme.{u}} [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    {SW : CoefficientDerivedSystemCalculus l E W}
    {SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))}
    (a : DualizingOperation (D := D) (hl := hl) W SW SS) :
    (domain l E W).FullSubcategory :=
  a.realization.G.obj (normalizedUnit (Spec (.of D.k)))

/-- The dualizing comparison is the evaluated exceptional comparison on the regular unit.
The unit comparison is fixed sectionwise before applying the exceptional functor.
Source: node proof step 9 (blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def DualizingOperation.finiteOmega {W : Scheme.{u}} [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    {SW : CoefficientDerivedSystemCalculus l E W}
    {SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))}
    (a : DualizingOperation (D := D) (hl := hl) W SW SS) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).obj a.omega.obj ≅
      integralDualizingFiniteTerm l E D W n :=
  (FiniteExceptional.domain l E W n).ι.mapIso
      ((a.realization.exceptionalEvaluation n).app (normalizedUnit (Spec (.of D.k)))) ≪≫
    (ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1))
      (integralDualizingCompactification D W)).mapIso
        (((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).mapDerivedCategorySingleFunctor
          0).app (ordinaryCoefficientUnit (Spec (.of D.k))) ≪≫
          (DerivedCategory.singleFunctor
            (normalizedDVRModules l E (Spec (.of D.k)) n) 0).mapIso (a.unitEvaluation n))

/-- The relative trace is the absolute structural-counit transpose, formed in the
ordinary derived system categories. Thus its definition precedes finite evaluation.
Source: node proof steps 9--12
(blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def structuralTrace
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    {SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))}
    (r : Realization l E D hl f c SX SZ SY)
    (aX : DualizingOperation (D := D) (hl := hl) X SX SS)
    (aY : DualizingOperation (D := D) (hl := hl) Y SY SS)
    (comp : r.F ⋙ aY.realization.F ≅ aX.realization.F) :
    r.F.obj aX.omega ⟶ aY.omega :=
  aY.realization.adjunction.homEquiv _ _
    (comp.hom.app aX.omega ≫
      aX.realization.adjunction.counit.app (normalizedUnit (Spec (.of D.k))))

/-- Duality is a natural isomorphism of SYSTEM functors. Its defining identity is the
uncurried tensor-Hom evaluation equation with the structural-counit trace. It fixes
the actual transpose, and its finite equation uses the prescribed finite trace.
Source: node proof steps 9--14
(blueprint: lem-coef-finite-adjunction-diagram-realization). -/
structure Duality
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    {SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))}
    (r : Realization l E D hl f c SX SZ SY)
    (aX : DualizingOperation (D := D) (hl := hl) X SX SS)
    (aY : DualizingOperation (D := D) (hl := hl) Y SY SS)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (g : Geometry l E f SX SY) where
  compactComposition : r.F ⋙ aY.realization.F ≅ aX.realization.F
  /-- No bound common to the levels occurs in this preservation assertion. -/
  dualPreservesX : ∀ M : (domain l E X).FullSubcategory,
    domain l E X ((dual X aX.omega.obj).obj (op M.obj))
  dualPreservesY : ∀ N : (domain l E Y).FullSubcategory,
    domain l E Y ((dual Y aY.omega.obj).obj (op N.obj))
  iso : r.G ⋙ (domain l E X).ι ≅
    (domain l E Y).ι ⋙ dualFormula (f := f) aX.omega.obj aY.omega.obj
  /-- The pullback of the system dual is normalized, without imposing a level bound. -/
  pullDualNormalized : ∀ N : (domain l E Y).FullSubcategory,
    IsNormalizedCoefficientSequence l E X
      ((integralComparisonDerivedSequencePullback l E f).obj
        ((dual Y aY.omega.obj).obj (op N.obj)))
  /-- This is the specified finite dual-formula map under canonical evaluation comparisons. -/
  finiteFormula : ∀ (n : ℕ) (N : (domain l E Y).FullSubcategory),
    (coefficientSequenceDerivedEvaluation l E X n).map (iso.hom.app N) ≫
      (SX.fiberHom
        ((integralComparisonDerivedSequencePullback l E f).obj
          ((dual Y aY.omega.obj).obj (op N.obj))) aX.omega.obj
        (pullDualNormalized N) aX.omega.property.1 n).hom ≫
      (coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom
          (((finiteDerivedPullback l E n f).map
              ((coefficientFiniteInternalHom l E Y n).map
                (Prod.mkHom (𝟙 _) (aY.finiteOmega n).inv)) ≫
            (finiteDerivedPullback l E n f).map
              (SY.fiberHom N.obj aY.omega.obj N.property.1 aY.omega.property.1 n).inv ≫
            (Geometry.pullEvaluation l E g n).inv.app ((dual Y aY.omega.obj).obj (op N.obj))).op)
          (aX.finiteOmega n).hom) =
      ((r.exceptionalEvaluation n).hom.app N).hom ≫
        (FiniteExceptional.dualFormulaIso l E D hl f c n).hom.app
          ((evaluation l E Y n).obj N)
  finiteTrace : ∀ n : ℕ,
    (coefficientSequenceDerivedEvaluation l E Y n).map
        (structuralTrace r aX aY compactComposition).hom ≫ (aY.finiteOmega n).hom =
      ((r.supportEvaluation n).hom.app aX.omega).hom ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          (aX.finiteOmega n).hom ≫ CoefDualFormulaScalarTranspose.finiteTrace D l E f c n
  /-- This is the finite-dual-formula equation BEFORE applying any evaluation. -/
  pairing : ∀ N : (domain l E Y).FullSubcategory,
    SY.systemClosed.tensor.map
        (Prod.mkHom (r.supportIso.hom.app (r.G.obj N))
          (𝟙 ((dual Y aY.omega.obj).obj (op N.obj)))) ≫
        r.support.projection (r.G.obj N).obj ((dual Y aY.omega.obj).obj (op N.obj)) ≫
        r.support.functor.map
          (SX.systemClosed.tensor.map (Prod.mkHom (iso.hom.app N) (𝟙 _)) ≫
            SX.systemClosed.evaluation
              ((integralComparisonDerivedSequencePullback l E f).obj
                ((dual Y aY.omega.obj).obj (op N.obj))) aX.omega.obj) ≫
        r.supportIso.inv.app aX.omega ≫
        (structuralTrace r aX aY compactComposition).hom =
      SY.systemClosed.tensor.map
          (Prod.mkHom (r.adjunction.counit.app N).hom
            (𝟙 ((dual Y aY.omega.obj).obj (op N.obj)))) ≫
        (swap l E SY βY N.obj ((dual Y aY.omega.obj).obj (op N.obj))).hom ≫
        SY.systemClosed.evaluation N.obj aY.omega.obj

/-- The reduction functor restricted to integral constructible inputs, using a proof of
its actual finite-Tor preservation rather than assuming a uniform system bound.
Source: node second paragraph and proof step 6
(blueprint: lem-coef-finite-adjunction-diagram-realization). -/
def reducedConstructible (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E W)
    (h : ∀ K : sfIntegralConstructibleCategory l E W, domain l E W (S.reduction.obj K.obj)) :
    sfIntegralConstructibleCategory l E W ⥤ (domain l E W).FullSubcategory :=
  (domain l E W).lift ((sfIntegralConstructible l E W).ι ⋙ S.reduction) h

/-- Functorial compact-support comparison, with the specified finite projections.
The only integral operation here is the already recorded compact-support functor.
Source: node second paragraph and proof step 6
(blueprint: lem-coef-finite-adjunction-diagram-realization). -/
structure IntegralSupport
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (r : Realization l E D hl f c SX SZ SY) where
  reductionPreserves : ∀ K : sfIntegralConstructibleCategory l E X,
    domain l E X (SX.reduction.obj K.obj)
  iso : reducedConstructible X SX reductionPreserves ⋙ r.F ⋙ (domain l E Y).ι ⋙
      coefficientSequenceLimit l E Y ≅
    sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E ⋙
      (sfIntegralConstructible l E Y).ι
  projections : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (coefficientSequenceProjection l E Y n).app
        (r.F.obj ((reducedConstructible X SX reductionPreserves).obj K)).obj ≫
      (coefficientFiniteDerivedRestriction l E Y n).map
        (((r.supportEvaluation n).hom.app
          ((reducedConstructible X SX reductionPreserves).obj K)).hom ≫
          (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
            ((SX.reductionEvaluation n).hom.app K.obj)) =
    iso.hom.app K ≫ (coefficientFiniteAdjunction l E Y n).unit.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c E).obj K).obj ≫
      (coefficientFiniteDerivedRestriction l E Y n).map
        (sfCompactSupportFiniteReductionIso l D.k (finiteFieldDatumPrimeUnit D l hl) c E K n).hom

variable (l E D hl f c)

/-- Functorial realization of finite exceptional operations, duality and enriched
adjunction on normalized derived coefficient systems, with no common level bound.
All displayed structures are conclusions; none is an additional hypothesis.

Source: current blueprint main-20261015, finite exceptional lemma and the first two
paragraphs of prop-coef-integral-exceptional-adjoint; Stacks 06YS, 0A95, 0941, 079P
(blueprint: lem-coef-finite-adjunction-diagram-realization).

Proof: work first with strict systems on the etale sequence site. Simultaneous
K-flat and K-injective resolutions give the ordinary unbounded derived system
category and exact evaluations. Exact open extension and proper total direct
image define compact support on systems. The open-unit tensor transpose is the
identity comparison on the open slice and is invertible; on the complementary
slice both terms vanish. The two quotient restrictions have the same canonical
quotient ring map on constant sections, hence agree after sheafification and
exact localization. These give the Support and QuotientRestriction proof fields.
Proper coproduct preservation at each
finite coefficient and componentwise coproducts make this functor coproduct
preserving. Grothendieck-derived Brown representability gives its actual right
adjoint. The derived evaluation left adjoints and the proper/open projection
comparison identify its evaluated adjoints, units, counits and quotient mates.
Transfer through the unbounded etale/pro-etale system comparison, using etale
origin separately at each constructible level. Restrict both functors to the full
normalized finite-Tor subcategories. Finite preservation gives the level conditions;
invertibility of the finite mate b gives normalization, without a common bound.
Reduction, compact support and total limit identify the already defined integral
compact-support FUNCTOR; the scalar-adjunction units give exactly its projections.
Apply the same system construction to the structure maps and coefficient unit.
The finite dualizing comparison identifies the resulting tower and its transitions;
the normalized tower's Roos presentation identifies its limit with the prescribed
dualizing construction, retaining the actual projections. Finite duality and
quotient tensor-Hom compatibility show that system internal dual preserves the
normalized finite-Tor domain. Form the relative trace by the absolute structural
counit and compact-support composition. On simultaneous system resolutions the
proper projection, open tensor, signed symmetry and evaluation give the displayed
pairing. Tensor-Hom transposition defines the dual-formula map; finite duality and
joint conservativity make it an isomorphism. The pairing is an equality of system
maps, so also preserves normalization and the finite evaluation pairings. Finally
form enrichedMap by projection, geometric counit, evaluation and exceptional
counit, BEFORE evaluating. Its finite values are the etale enriched-adjunction
transposes transported by canonical site comparison. Conservativity makes this
map invertible. Derived global sections of its inverse and the ordinary
section/direct-image comparison give globalMap, hence the natural isomorphism
iso. Universal derived units prove its representative normalization and the finite
evaluation square. The finite Hom identification is precisely the already fixed
finite adjunction. All inverses and triangle and transpose identities hold in the
ordinary derived system categories before taking any total inverse limit. -/
theorem finiteAdjunctionDiagramRealization :
    ∃ (SX : CoefficientDerivedSystemCalculus l E X)
      (SZ : CoefficientDerivedSystemCalculus l E c.Z)
      (SY : CoefficientDerivedSystemCalculus l E Y)
      (SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))),
      Nonempty (CoefficientDerivedSystemCoherence l E X SX) ∧
      Nonempty (CoefficientDerivedSystemCoherence l E c.Z SZ) ∧
      Nonempty (CoefficientDerivedSystemCoherence l E Y SY) ∧
      Nonempty (CoefficientDerivedSystemCoherence l E (Spec (.of D.k)) SS) ∧
      ∃ (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
        (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
        (r : Realization l E D hl f c SX SZ SY)
        (g : Geometry l E f SX SY) (s : SectionsPush g)
        (aX : DualizingOperation (D := D) (hl := hl) X SX SS)
        (aY : DualizingOperation (D := D) (hl := hl) Y SY SS),
        Nonempty (RingedDerivedTensorCoherence.{u+1, u, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X) SX.systemClosed SX.systemTensorModel βX) ∧
        Nonempty (RingedDerivedTensorCoherence.{u+1, u, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) SY.systemClosed SY.systemTensorModel βY) ∧
        Nonempty (Enriched r g s βX βY) ∧ Nonempty (Duality r aX aY βY g) ∧
        Nonempty (IntegralSupport r) := by
  sorry

end WeilConjectures.FiniteAdjunctionDiagram
