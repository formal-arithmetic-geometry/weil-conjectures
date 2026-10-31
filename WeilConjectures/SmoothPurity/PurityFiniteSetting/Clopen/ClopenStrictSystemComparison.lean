/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenDerivedDecomposition
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Compactification.Defs

/-! # Normalized strict-system comparison on a clopen component

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/def-pur-section-invariant.md, finite-clopen compactification
and adjunction argument (blueprint: def-pur-clopen-strict-system-comparison).

The statement uses the canonical intrinsic pro-etale operations.  At a finite
coefficient level, compact support is the specified compactification formula and
exceptional inverse image is `PurityFiniteSetting.exceptionalInverseImage`.  The
component maps are the actual derived pullbacks from the clopen decomposition.
The coefficient-system, integral inverse-limit, rational, common-stage, and
coefficient-unit clauses are the corresponding transported comparisons described
in the node proof; no smoothness, orientation, section, or tensor-invertibility
hypothesis is introduced.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w c ci d v vi vd

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace WeilConjectures.PurityFiniteSetting

/-- The valuation ring lifted into the unchanged small-site coefficient universe.
Source: blueprint coefficient size convention
(blueprint: def-pur-clopen-strict-system-comparison). -/
abbrev clopenSystemRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :=
  ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)

/-- The same uniformizer in the lifted ring; the positive level is `n+1`.
Source: blueprint coefficient size convention
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def clopenSystemUniformizer (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    clopenSystemRing l E := ULift.up (Padic.coefficientExtensionUniformizer l E)

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance (priority := 5000) clopenProEtaleCommRingSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} := inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance (priority := 5000) clopenProEtaleAddCommGrpLocal (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance (priority := 5000) clopenProEtaleTypeSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) (Type (u + 1)) := inferInstance

/-- The actual strict pro-etale coefficient-system category, at the original site size.
Source: blueprint proof steps 8--9
(blueprint: def-pur-clopen-strict-system-comparison). -/
abbrev ClopenProEtaleSystem (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :=
  SheafOfModules.CoefficientSystem (J := Scheme.ProEt.topology X)
    (clopenSystemRing l E) (clopenSystemUniformizer l E)

/-- Standard localization of the actual strict systems.
Source: Stacks 05RU (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance clopenProEtaleSystemDerived
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    HasDerivedCategory.{u + 2} (ClopenProEtaleSystem l E X) :=
  HasDerivedCategory.standard _

/-- The standard finite-level localization, with no universe identification imposed.
Source: Stacks 05RU (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance clopenProEtaleLevelDerived
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (n : ℕ) :
    HasDerivedCategory.{u + 2}
      (SheafOfModules.coefficientLevelModules (J := Scheme.ProEt.topology X)
        (clopenSystemRing l E) (clopenSystemUniformizer l E) n) :=
  HasDerivedCategory.standard _

/-- Cache the actual small-site witness at its specified universe.
Source: blueprint size convention
(blueprint: def-pur-clopen-strict-system-comparison). -/
instance (priority := 5000) clopenProEtaleSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- Cache the unchanged sequence-site witness at the same specified universe.
Source: blueprint size convention
(blueprint: def-pur-clopen-strict-system-comparison). -/
instance (priority := 5000) clopenSequenceSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × X.ProEt) := essentiallySmallSelf.{0, u, u + 1} _

/-- The two equivalent presentations of actual strict pro-etale systems.
The ring maps are fixed on quotient generators. Evaluation and transition equations
fix the ordinary equivalence; the derived functor is its exact localization.
This is a presentation of systems, never a lift of an ordinary derived diagram.
Source: Stacks 0941 and blueprint proof steps 8--9
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure ClopenSequenceRealizationData
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) where
  ringIso : ∀ n : ℕ, integralCoefficientCommRingSheaf.{u, u} l E X n ≅
    SheafOfModules.coefficientQuotientSheaf.{u + 1, u, u + 1} (J := Scheme.ProEt.topology X)
      (clopenSystemRing l E) (clopenSystemUniformizer l E) n
  level : ∀ n : ℕ,
    SheafOfModules.coefficientLevelModules (J := Scheme.ProEt.topology X)
      (clopenSystemRing l E) (clopenSystemUniformizer l E) n ⥤
        normalizedDVRModules.{u, u} l E X n
  levelRestriction : ∀ {m n : ℕ} (h : n ≤ m),
    SheafOfModules.coefficientRestriction (J := Scheme.ProEt.topology X)
      (clopenSystemRing l E) (clopenSystemUniformizer l E) h ⋙ level m ≅
        level n ⋙ normalizedDVRModuleRes.{u, u} l E X h
  ordinary : ClopenProEtaleSystem l E X ≌ coefficientSequenceModules.{u, u} l E X
  [ordinaryAdditive : ordinary.functor.Additive]
  evaluation : ∀ n : ℕ,
    ordinary.functor ⋙ coefficientSequenceEvaluation.{u, u} l E X n ≅
      SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X)
        (O := clopenSystemRing l E) (ell := clopenSystemUniformizer l E) n ⋙ level n
  derived : DerivedCategory (ClopenProEtaleSystem l E X) ≌ coefficientSequenceDerived.{u, u} l E X
  factors : DerivedCategory.Q ⋙ derived.functor ≅
    ordinary.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The normalization equations for `ClopenSequenceRealizationData`.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
def ClopenSequenceRealizationCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (record : ClopenSequenceRealizationData l E X) : Prop :=
  -- ringGenerators
  (∀ n : ℕ,
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1, u, u}
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))))) ≫
        (record.ringIso n).hom =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk
          ((Ideal.span ({clopenSystemUniformizer l E} : Set (clopenSystemRing l E))) ^
            (n + 1))))) ∧
  -- level_eq
  (∀ n : ℕ, record.level n = SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (record.ringIso n).hom)) ∧
  -- levelRestrictionUnderlying
  (∀ {m n : ℕ} (h : n ≤ m)
    (M : SheafOfModules.coefficientLevelModules (J := Scheme.ProEt.topology X)
      (clopenSystemRing l E) (clopenSystemUniformizer l E) n) (U : X.ProEtᵒᵖ),
    HEq (((SheafOfModules.toSheaf (integralCoefficientSheaf l E X m)).map
      ((record.levelRestriction h).hom.app M)).hom.app U)
      (𝟙 (((SheafOfModules.toSheaf (integralCoefficientSheaf l E X m)).obj
        ((record.level m).obj ((SheafOfModules.coefficientRestriction
          (J := Scheme.ProEt.topology X) (clopenSystemRing l E)
          (clopenSystemUniformizer l E) h).obj M))).obj.obj U))) ∧
  -- transition
  (∀ (n : ℕ) (M : ClopenProEtaleSystem l E X),
    (coefficientSequenceTransition.{u, u} l E X (Nat.le_succ n)).app
      (record.ordinary.functor.obj M) ≫
        (normalizedDVRModuleRes.{u, u} l E X (Nat.le_succ n)).map ((record.evaluation
      n).hom.app M) =
      (record.evaluation (n + 1)).hom.app M ≫ (record.level (n + 1)).map (M.transition n) ≫
        (record.levelRestriction (Nat.le_succ n)).hom.app (M.level n))

/-- The actual comparison data together with all its normalization equations.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure ClopenSequenceRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    extends ClopenSequenceRealizationData l E X where
  coherence : ClopenSequenceRealizationCoherence l E X toClopenSequenceRealizationData

attribute [instance] ClopenSequenceRealizationData.ordinaryAdditive

/-- The actual etale/pro-etale system comparison with its geometric normalization.
All ordinary, derived, evaluation, scalar and transition data are the full recorded
system-comparison interface, not a freely chosen functor between system categories.
Source: Zheng Lemma 4.10 and blueprint proof step 8
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure ClopenSystemComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (PX : StrictEtaleEvaluation X (clopenSystemRing l E) (clopenSystemUniformizer l E)) where
  proEtaleEvaluation : SheafOfModules.CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
    (J := Scheme.ProEt.topology X)
    (O := clopenSystemRing l E) (ell := clopenSystemUniformizer l E)
  ordinary : SheafOfModules.CoefficientSystemOrdinaryImage.{u + 1, u, u + 1, u, u + 1}
    (J := X.smallEtaleTopology) (K := Scheme.ProEt.topology X)
    (clopenSystemRing l E) (clopenSystemUniformizer l E)
    _ _ (Scheme.proEtaleSiteComparison X)
  derived : SheafOfModules.CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
    (J := X.smallEtaleTopology) (K := Scheme.ProEt.topology X)
    (clopenSystemRing l E) (clopenSystemUniformizer l E)
    _ _ (Scheme.proEtaleSiteComparison X) ordinary PX proEtaleEvaluation
  sequence : ClopenSequenceRealization l E X

end WeilConjectures.PurityFiniteSetting
