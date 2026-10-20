/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.FiniteClopenDerivedDecomposition
public import Sheaf.Paper.FiniteCompactSupportConstructibility
public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
public import Sheaf.Paper.EtaleCoefficientSystemAdjoint
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
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

/-- The finite direct sum in the statement is made functorial by the standard
pointwise biproduct construction.  The component functors all have the same
target category, so this is the right categorical rendering of the displayed
finite sum (including the empty index case).
Source: blueprint compact-support decomposition, proof steps 2--3
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def finiteBiproductFunctor {C : Type u} [Category.{v} C]
    {D : Type u} [Category.{vd} D] [HasZeroMorphisms D]
    {I : Type w} [Finite I] [HasFiniteBiproducts D]
    (F : I → C ⥤ D) : C ⥤ D where
  obj X := ⨁ fun i => (F i).obj X
  map f := biproduct.map (fun i => (F i).map f)
  map_id X := by ext i; simp
  map_comp f g := by ext i; simp

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
noncomputable instance (priority := 5000) clopenProEtaleAddCommGrpSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance (priority := 5000) clopenProEtaleAddCommGrpLocal (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance (priority := 5000) clopenProEtaleRingCompose (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance (priority := 5000) clopenProEtaleTypeSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) (Type (u + 1)) := inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance (priority := 5000) clopenProEtaleRingSetCompose (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1}) :=
      inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance (priority := 5000) clopenProEtaleAddCommGrpSetCompose (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      inferInstance

/-- Every positive finite coefficient quotient is finite, as in the recorded coefficient datum.
Source: blueprint finite coefficient convention
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance clopenFiniteRingFinite (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

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

/-- Cache the existing standard sequence localization; no new derived category is used.
Source: Stacks 05RU (blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable instance (priority := 5000) clopenSequenceDerived
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    HasDerivedCategory.{u + 2} (coefficientSequenceModules.{u, u} l E X) :=
  HasDerivedCategory.standard _

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

/-- The exact formula for the actual system T_g used in integral exceptional image:
reduction, R nu_*, the strict etale right adjoint, nu^*, and the equivalent sequence
presentation. The reduction is the recorded single-K-flat construction.
Source: definition of exceptional inverse image and blueprint proof step 9
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def clopenExceptionalSystem
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {g : X ⟶ Y} {c : Compactification g}
    (S : StrictEtaleCompactSupport (clopenSystemRing l E) (clopenSystemUniformizer l E) c)
    (G : StrictEtaleExceptionalAdjoint _ _ c S)
    (CX : ClopenSystemComparison l E X S.PX)
    (CY : ClopenSystemComparison l E Y S.PY) :
    sfIntegralConstructibleCategory l E Y ⥤ coefficientSequenceDerived.{u, u} l E X :=
  (sfIntegralConstructible l E Y).ι ⋙
    (coefficientDerivedSystemEvaluationCalculus.{u, u} l E Y).choose.reduction ⋙
    CY.sequence.derived.inverse ⋙ CY.derived.system.direct ⋙ G.right ⋙
    CX.derived.system.inverse ⋙ CX.sequence.derived.functor

/-- The canonical system input R nu_* R_Y, retaining the actual reduction system.
Source: definition of integral exceptional inverse image
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def clopenExceptionalInput
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : Scheme.{u})
    (PY : StrictEtaleEvaluation Y (clopenSystemRing l E) (clopenSystemUniformizer l E))
    (CY : ClopenSystemComparison l E Y PY) :=
  (sfIntegralConstructible l E Y).ι ⋙
    (coefficientDerivedSystemEvaluationCalculus.{u, u} l E Y).choose.reduction ⋙
    CY.sequence.derived.inverse ⋙ CY.derived.system.direct

/-- Integral component restriction is the recorded completed derived pullback.
The residue-field units follow from the fixed characteristic convention.
Source: blueprint proof step 9
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def clopenIntegralRestriction (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    {Xi X : Over (Spec (.of P.field.k))} (j : Xi ⟶ X) :=
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  letI := fun x : Xi.left ↦ (P.clopenResidue_isUnit Xi x).invertible
  constructibleIntegralPullback P.coefficients.l E j.left

/-- Rational component restriction is the recorded raw localized pullback.
Source: blueprint proof step 10
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def clopenRationalRestriction (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    {Xi X : Over (Spec (.of P.field.k))} (j : Xi ⟶ X) :=
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  letI := fun x : Xi.left ↦ (P.clopenResidue_isUnit Xi x).invertible
  rationalDerivedPullback P.coefficients.l E j.left

/-- The existing intrinsic exceptional operation at every positive finite level.
Source: finite exceptional-image definition
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable abbrev clopenFiniteExceptional (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (n : ℕ) :=
  Scheme.finiteExceptionalInverseImage P.coefficients.l E (n + 1) (Nat.succ_pos n)
    P.field.k X.left Y.left g

/-- The actual integral coefficient unit at an arbitrary finite coefficient field.
Source: blueprint coefficient-unit clause
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def clopenIntegralUnitAt (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E] (Y : Scheme.{u}) :
    sfIntegralConstructibleCategory P.coefficients.l E Y :=
  ⟨integralConstantCoefficientObject P.coefficients.l E Y,
    (integralConstantCoefficient_constructible P.coefficients.l E Y
      P.field P.coefficients.different).2.1⟩

/-- Inclusion of the recorded bounded constructible finite-coefficient category.
Source: blueprint Dbc input convention
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable abbrev clopenFiniteInclusion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) (n : ℕ) :=
  (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y).ι

/-- The actual finite reduction, restricted to its known constructible values.
Source: blueprint definition of integral Dbc and finite-evaluation clause
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def clopenConstructibleReduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) (n : ℕ) :=
  (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y).lift
    ((sfIntegralConstructible l E Y).ι ⋙ scalarReductionDerivedExtension l E Y n)
    (fun K ↦ (K.property.2.choose_spec.choose_spec.2 n).1)

/-- The finite coefficient unit as an object of the same Dbc input category.
Source: blueprint coefficient-unit clause
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def clopenFiniteUnitAt (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) (n : ℕ) :=
  (⟨finiteConstantCoefficientObject l E Y n,
    (finiteConstantCoefficient_constructible l E Y n).1⟩ :
    (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y).FullSubcategory)

/-- The component right-adjoint comparison, normalized by its actual counit equation.
Here `insertion` is zero insertion, `restriction` is component restriction, and `b`
is the compact-support composition comparison. Source: blueprint finite-clopen
compactification argument, proof step 4
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure ClopenCounitComparisonData
    {C : Type c} {Ci : Type ci} {D : Type d}
    [Category.{v} C] [Category.{vi} Ci] [Category.{vd} D]
    (insertion : Ci ⥤ C) (restriction : C ⥤ Ci)
    (F : C ⥤ D) (G : D ⥤ C) (Fi : Ci ⥤ D) (Gi : D ⥤ Ci)
    (componentAdj : insertion ⊣ restriction)
    (adj : F ⊣ G) (adjI : Fi ⊣ Gi) where
  compactSupport : insertion ⋙ F ≅ Fi
  comparison : G ⋙ restriction ≅ Gi

/-- The normalization equations for `ClopenCounitComparisonData`.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
def ClopenCounitComparisonCoherence
    {C : Type c} {Ci : Type ci} {D : Type d}
    [Category.{v} C] [Category.{vi} Ci] [Category.{vd} D]
    (insertion : Ci ⥤ C) (restriction : C ⥤ Ci)
    (F : C ⥤ D) (G : D ⥤ C) (Fi : Ci ⥤ D) (Gi : D ⥤ Ci)
    (componentAdj : insertion ⊣ restriction)
    (adj : F ⊣ G) (adjI : Fi ⊣ Gi)
    (record : ClopenCounitComparisonData insertion restriction F G Fi Gi componentAdj adj adjI)
      : Prop :=
  -- counit
  (∀ L : D,
    Fi.map (record.comparison.hom.app L) ≫ adjI.counit.app L =
      record.compactSupport.inv.app (restriction.obj (G.obj L)) ≫
        F.map (componentAdj.counit.app (G.obj L)) ≫ adj.counit.app L)

/-- The actual comparison data together with all its normalization equations.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure ClopenCounitComparison
    {C : Type c} {Ci : Type ci} {D : Type d}
    [Category.{v} C] [Category.{vi} Ci] [Category.{vd} D]
    (insertion : Ci ⥤ C) (restriction : C ⥤ Ci)
    (F : C ⥤ D) (G : D ⥤ C) (Fi : Ci ⥤ D) (Gi : D ⥤ Ci)
    (componentAdj : insertion ⊣ restriction)
    (adj : F ⊣ G) (adjI : Fi ⊣ Gi)
    extends ClopenCounitComparisonData insertion restriction F G Fi Gi componentAdj adj adjI where
  coherence : ClopenCounitComparisonCoherence insertion restriction F G Fi Gi componentAdj adj
      adjI toClopenCounitComparisonData

/-- The strict-system comparison and its finite evaluations, with the specified
adjunction mates. These are actual derived strict systems and their morphisms.
Both system and level comparisons satisfy the same counit normalization.
Source: blueprint finite-clopen compactification argument, proof steps 5--8
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure StrictClopenExceptionalComparisonData
    (O : Type (u + 1)) [CommRing O] (ell : O)
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (S : StrictEtaleCompactSupport O ell c)
    (G : StrictEtaleExceptionalAdjoint O ell c S)
    (Si : StrictEtaleCompactSupport O ell (c.precomp j))
    (Gi : StrictEtaleExceptionalAdjoint O ell (c.precomp j) Si) where
  sameTargetEvaluation : Si.PY = S.PY
  restriction : StrictEtaleOrdinaryImage O ell j
  derivedRestriction :
    SheafOfModules.CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
    (J := X.smallEtaleTopology) (K := Xi.smallEtaleTopology) O ell _ _ _ restriction S.PX Si.PX
  insertionAdjunction : derivedRestriction.system.direct ⊣ derivedRestriction.system.inverse
  system : ClopenCounitComparison
    derivedRestriction.system.direct derivedRestriction.system.inverse
    S.functor G.right Si.functor Gi.right insertionAdjunction G.adjunction Gi.adjunction
  levelInsertionAdjunction : ∀ n : ℕ,
    (derivedRestriction.level n).direct ⊣ (derivedRestriction.level n).inverse
  level : ∀ n : ℕ, ClopenCounitComparison
    (derivedRestriction.level n).direct (derivedRestriction.level n).inverse
    (S.levelFunctor n) (G.levelRight n) (Si.levelFunctor n) (Gi.levelRight n)
    (levelInsertionAdjunction n) (G.levelAdjunction n) (Gi.levelAdjunction n)

/-- The normalization equations for `StrictClopenExceptionalComparisonData`.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
def StrictClopenExceptionalComparisonCoherence
    (O : Type (u + 1)) [CommRing O] (ell : O)
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (S : StrictEtaleCompactSupport O ell c)
    (G : StrictEtaleExceptionalAdjoint O ell c S)
    (Si : StrictEtaleCompactSupport O ell (c.precomp j))
    (Gi : StrictEtaleExceptionalAdjoint O ell (c.precomp j) Si)
    (record : StrictClopenExceptionalComparisonData O ell c j S G Si Gi) : Prop :=
  -- evaluation
  (∀ (n : ℕ) (L : DerivedCategory (strictEtaleCoefficientSystem Y O ell)),
    (Si.PX.evaluation n).map (record.system.comparison.hom.app L) ≫
        (Gi.evaluation n).hom.app L =
      (record.derivedRestriction.inverseEvaluation n).hom.app (G.right.obj L) ≫
        (record.derivedRestriction.level n).inverse.map ((G.evaluation n).hom.app L) ≫
        (record.level n).comparison.hom.app ((S.PY.evaluation n).obj L) ≫
        (Gi.levelRight n).map
          (eqToHom (congrArg (fun Q ↦ (Q.evaluation n).obj L) record.sameTargetEvaluation.symm)))

/-- The actual comparison data together with all its normalization equations.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure StrictClopenExceptionalComparison
    (O : Type (u + 1)) [CommRing O] (ell : O)
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (S : StrictEtaleCompactSupport O ell c)
    (G : StrictEtaleExceptionalAdjoint O ell c S)
    (Si : StrictEtaleCompactSupport O ell (c.precomp j))
    (Gi : StrictEtaleExceptionalAdjoint O ell (c.precomp j) Si)
    extends StrictClopenExceptionalComparisonData O ell c j S G Si Gi where
  coherence : StrictClopenExceptionalComparisonCoherence O ell c j S G Si Gi
      toStrictClopenExceptionalComparisonData

/-- The component insertion uses the inverse of the canonical restriction counit;
this removes rescalings of the reverse adjunction. The open composition is fixed
by its right mate, and the compact-support map is its image under the common
proper direct image. Source: blueprint proof steps 2--7
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure StrictClopenCompactSupportNormalizationData
    (O : Type (u + 1)) [CommRing O] (ell : O)
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (S : StrictEtaleCompactSupport O ell c)
    (G : StrictEtaleExceptionalAdjoint O ell c S)
    (Si : StrictEtaleCompactSupport O ell (c.precomp j))
    (Gi : StrictEtaleExceptionalAdjoint O ell (c.precomp j) Si)
    (R : StrictClopenExceptionalComparison O ell c j S G Si Gi) where
  restrictionCounit : IsIso R.derivedRestriction.system.adjunction.counit
  levelRestrictionCounit : ∀ n, IsIso (R.derivedRestriction.level n).adjunction.counit
  sameProper : HEq Si.properDerived S.properDerived
  ordinaryRight : S.openImage.inverse ⋙ R.restriction.inverse ≅ Si.openImage.inverse
  levelRight : ∀ n, (S.openImage.lift n).modules ⋙ (R.restriction.lift n).modules ≅
    (Si.openImage.lift n).modules
  right : S.openDerived.system.inverse ⋙ R.derivedRestriction.system.inverse ≅
    Si.openDerived.system.inverse
  openComparison : R.derivedRestriction.system.direct ⋙ S.derivedOpen ≅ Si.derivedOpen

/-- The normalization equations for `StrictClopenCompactSupportNormalizationData`.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
def StrictClopenCompactSupportNormalizationCoherence
    (O : Type (u + 1)) [CommRing O] (ell : O)
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (S : StrictEtaleCompactSupport O ell c)
    (G : StrictEtaleExceptionalAdjoint O ell c S)
    (Si : StrictEtaleCompactSupport O ell (c.precomp j))
    (Gi : StrictEtaleExceptionalAdjoint O ell (c.precomp j) Si)
    (R : StrictClopenExceptionalComparison O ell c j S G Si Gi)
    (record : StrictClopenCompactSupportNormalizationData O ell c j S G Si Gi R) : Prop :=
  -- insertionUnit
  (R.insertionAdjunction.unit =
    @inv _ _ _ _ R.derivedRestriction.system.adjunction.counit record.restrictionCounit) ∧
  -- levelInsertionUnit
  (∀ n, (R.levelInsertionAdjunction n).unit =
    @inv _ _ _ _ (R.derivedRestriction.level n).adjunction.counit
      (record.levelRestrictionCounit n)) ∧
  -- underlying
  (∀ (n : ℕ) (M : strictEtaleLevel c.Z O ell n),
    (SheafOfModules.coefficientUnderlying (J := Xi.smallEtaleTopology) O ell n).map
        ((record.levelRight n).hom.app M) ≫
        (Si.openImage.lift n).moduleUnderlying.hom.app M =
      (R.restriction.lift n).moduleUnderlying.hom.app ((S.openImage.lift n).modules.obj M) ≫
        (Scheme.etaleSetPullback j).map ((S.openImage.lift n).moduleUnderlying.hom.app M) ≫
        (ProEtale.etaleComparisonComp (Type (u + 1)) j c.i).inv.app
          ((SheafOfModules.coefficientUnderlying (J := c.Z.smallEtaleTopology) O ell n).obj M)) ∧
  -- ordinaryEvaluation
  (∀ (n : ℕ) (M : strictEtaleCoefficientSystem c.Z O ell),
    (SheafOfModules.coefficientEvaluation (J := Xi.smallEtaleTopology)
      (O := O) (ell := ell) n).map (record.ordinaryRight.hom.app M) ≫
        (Si.openImage.inverseEvaluation n).hom.app M =
      (R.restriction.inverseEvaluation n).hom.app (S.openImage.inverse.obj M) ≫
        (R.restriction.lift n).modules.map ((S.openImage.inverseEvaluation n).hom.app M) ≫
        (record.levelRight n).hom.app (M.level n)) ∧
  -- rightFactors
  (∀ H : CochainComplex (strictEtaleCoefficientSystem c.Z O ell) ℤ,
    record.right.hom.app (DerivedCategory.Q.obj H) ≫
      Si.openDerived.system.inverseFactors.hom.app H =
      R.derivedRestriction.system.inverse.map (S.openDerived.system.inverseFactors.hom.app H) ≫
        R.derivedRestriction.system.inverseFactors.hom.app
          ((S.openImage.inverse.mapHomologicalComplex (.up ℤ)).obj H) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex record.ordinaryRight (.up
      ℤ)).hom.app H)) ∧
  -- openCounit
  (∀ N : DerivedCategory (strictEtaleCoefficientSystem c.Z O ell),
    Si.derivedOpen.map (record.right.hom.app N) ≫ Si.derivedOpenAdjunction.counit.app N =
      record.openComparison.inv.app
          ((R.derivedRestriction.system.inverse).obj (S.openDerived.system.inverse.obj N)) ≫
        (R.insertionAdjunction.comp S.derivedOpenAdjunction).counit.app N) ∧
  -- supportMap
  (HEq R.system.compactSupport.hom
    (Functor.whiskerRight record.openComparison.hom S.properDerived.system.direct))

/-- The actual comparison data together with all its normalization equations.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure StrictClopenCompactSupportNormalization
    (O : Type (u + 1)) [CommRing O] (ell : O)
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j]
    (S : StrictEtaleCompactSupport O ell c)
    (G : StrictEtaleExceptionalAdjoint O ell c S)
    (Si : StrictEtaleCompactSupport O ell (c.precomp j))
    (Gi : StrictEtaleExceptionalAdjoint O ell (c.precomp j) Si)
    (R : StrictClopenExceptionalComparison O ell c j S G Si Gi)
    extends StrictClopenCompactSupportNormalizationData O ell c j S G Si Gi R where
  coherence : StrictClopenCompactSupportNormalizationCoherence O ell c j S G Si Gi R
      toStrictClopenCompactSupportNormalizationData

/-- The comparison-site square on actual strict systems. The ordinary square is
fixed on every underlying finite-level sheaf by the canonical geometric square;
the derived square is the localization of that very ordinary square.
Source: blueprint proof step 8; comparison-pullback functoriality
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure ClopenSystemSquareData
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} {c : Compactification g}
    {j : Xi ⟶ X} [IsOpenImmersion j] [IsClosedImmersion j]
    {S : StrictEtaleCompactSupport (clopenSystemRing l E) (clopenSystemUniformizer l E) c}
    {G : StrictEtaleExceptionalAdjoint _ _ c S}
    {Si : StrictEtaleCompactSupport _ _ (c.precomp j)}
    {Gi : StrictEtaleExceptionalAdjoint _ _ (c.precomp j) Si}
    (R : StrictClopenExceptionalComparison _ _ c j S G Si Gi)
    (CX : ClopenSystemComparison l E X S.PX)
    (Ci : ClopenSystemComparison l E Xi Si.PX) where
  ordinary : SheafOfModules.CoefficientSystemOrdinaryImage.{u + 1, u, u + 1, u, u + 1}
    (J := Scheme.ProEt.topology X) (K := Scheme.ProEt.topology Xi)
    (clopenSystemRing l E) (clopenSystemUniformizer l E)
    _ _ (Scheme.proEtaleSheafAdjunction j (Type (u + 1)))
  derived : SheafOfModules.CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
    (J := Scheme.ProEt.topology X) (K := Scheme.ProEt.topology Xi)
    (clopenSystemRing l E) (clopenSystemUniformizer l E)
    _ _ (Scheme.proEtaleSheafAdjunction j (Type (u + 1))) ordinary
    CX.proEtaleEvaluation Ci.proEtaleEvaluation
  ordinarySquare : CX.ordinary.inverse ⋙ ordinary.inverse ≅
    R.restriction.inverse ⋙ Ci.ordinary.inverse
  levelSquare : ∀ n : ℕ,
    (CX.ordinary.lift n).modules ⋙ (ordinary.lift n).modules ≅
      (R.restriction.lift n).modules ⋙ (Ci.ordinary.lift n).modules
  square : CX.derived.system.inverse ⋙ derived.system.inverse ≅
    R.derivedRestriction.system.inverse ⋙ Ci.derived.system.inverse

/-- The normalization equations for `ClopenSystemSquareData`.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
def ClopenSystemSquareCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} {c : Compactification g}
    {j : Xi ⟶ X} [IsOpenImmersion j] [IsClosedImmersion j]
    {S : StrictEtaleCompactSupport (clopenSystemRing l E) (clopenSystemUniformizer l E) c}
    {G : StrictEtaleExceptionalAdjoint _ _ c S}
    {Si : StrictEtaleCompactSupport _ _ (c.precomp j)}
    {Gi : StrictEtaleExceptionalAdjoint _ _ (c.precomp j) Si}
    (R : StrictClopenExceptionalComparison _ _ c j S G Si Gi)
    (CX : ClopenSystemComparison l E X S.PX)
    (Ci : ClopenSystemComparison l E Xi Si.PX)
    (record : ClopenSystemSquareData l E R CX Ci) : Prop :=
  -- levelUnderlying
  (∀ (n : ℕ)
    (M : SheafOfModules.coefficientLevelModules (J := X.smallEtaleTopology)
      (clopenSystemRing l E) (clopenSystemUniformizer l E) n),
    (SheafOfModules.coefficientUnderlying (J := Scheme.ProEt.topology Xi)
      (clopenSystemRing l E) (clopenSystemUniformizer l E) n).map
        ((record.levelSquare n).hom.app M) ≫
        (Ci.ordinary.lift n).moduleUnderlying.hom.app
          ((R.restriction.lift n).modules.obj M) ≫
        (ProEtale.comparisonCoefficientPullback (Type (u + 1)) Xi).map
          ((R.restriction.lift n).moduleUnderlying.hom.app M) =
      (record.ordinary.lift n).moduleUnderlying.hom.app ((CX.ordinary.lift n).modules.obj M) ≫
        (Scheme.proEtaleSheafInverseImage j (Type (u + 1))).map
          ((CX.ordinary.lift n).moduleUnderlying.hom.app M) ≫
        (ProEtale.comparisonCoefficientPullbackIso (Type (u + 1)) j).inv.app
          ((SheafOfModules.coefficientUnderlying (J := X.smallEtaleTopology)
            (clopenSystemRing l E) (clopenSystemUniformizer l E) n).obj M)) ∧
  -- ordinaryEvaluation
  (∀ (n : ℕ)
    (M : strictEtaleCoefficientSystem X (clopenSystemRing l E) (clopenSystemUniformizer l E)),
    (SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology Xi)
      (O := clopenSystemRing l E) (ell := clopenSystemUniformizer l E) n).map
        (record.ordinarySquare.hom.app M) ≫
        (Ci.ordinary.inverseEvaluation n).hom.app (R.restriction.inverse.obj M) ≫
        (Ci.ordinary.lift n).modules.map ((R.restriction.inverseEvaluation n).hom.app M) =
      (record.ordinary.inverseEvaluation n).hom.app (CX.ordinary.inverse.obj M) ≫
        (record.ordinary.lift n).modules.map ((CX.ordinary.inverseEvaluation n).hom.app M) ≫
        (record.levelSquare n).hom.app (M.level n)) ∧
  -- factors
  (∀ H : CochainComplex
    (strictEtaleCoefficientSystem X (clopenSystemRing l E) (clopenSystemUniformizer l E)) ℤ,
    record.square.hom.app (DerivedCategory.Q.obj H) ≫
        Ci.derived.system.inverse.map
          (R.derivedRestriction.system.inverseFactors.hom.app H) ≫
        Ci.derived.system.inverseFactors.hom.app
          ((R.restriction.inverse.mapHomologicalComplex (.up ℤ)).obj H) =
      record.derived.system.inverse.map (CX.derived.system.inverseFactors.hom.app H) ≫
        record.derived.system.inverseFactors.hom.app
          ((CX.ordinary.inverse.mapHomologicalComplex (.up ℤ)).obj H) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex record.ordinarySquare (.up ℤ)).hom.app H))

/-- The actual comparison data together with all its normalization equations.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: def-pur-clopen-strict-system-comparison). -/
structure ClopenSystemSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} {c : Compactification g}
    {j : Xi ⟶ X} [IsOpenImmersion j] [IsClosedImmersion j]
    {S : StrictEtaleCompactSupport (clopenSystemRing l E) (clopenSystemUniformizer l E) c}
    {G : StrictEtaleExceptionalAdjoint _ _ c S}
    {Si : StrictEtaleCompactSupport _ _ (c.precomp j)}
    {Gi : StrictEtaleExceptionalAdjoint _ _ (c.precomp j) Si}
    (R : StrictClopenExceptionalComparison _ _ c j S G Si Gi)
    (CX : ClopenSystemComparison l E X S.PX)
    (Ci : ClopenSystemComparison l E Xi Si.PX)
    extends ClopenSystemSquareData l E R CX Ci where
  coherence : ClopenSystemSquareCoherence l E R CX Ci toClopenSystemSquareData

/-- Component restriction in the sequence presentation is conjugate to the actual
geometric inverse image on strict systems. Source: blueprint proof steps 8--9
(blueprint: def-pur-clopen-strict-system-comparison). -/
noncomputable def ClopenSystemSquare.sequenceRestriction
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} {c : Compactification g}
    {j : Xi ⟶ X} [IsOpenImmersion j] [IsClosedImmersion j]
    {S : StrictEtaleCompactSupport (clopenSystemRing l E) (clopenSystemUniformizer l E) c}
    {G : StrictEtaleExceptionalAdjoint _ _ c S}
    {Si : StrictEtaleCompactSupport _ _ (c.precomp j)}
    {Gi : StrictEtaleExceptionalAdjoint _ _ (c.precomp j) Si}
    {R : StrictClopenExceptionalComparison _ _ c j S G Si Gi}
    {CX : ClopenSystemComparison l E X S.PX}
    {Ci : ClopenSystemComparison l E Xi Si.PX}
    (Q : ClopenSystemSquare l E R CX Ci) :=
  CX.sequence.derived.inverse ⋙ Q.derived.system.inverse ⋙ Ci.sequence.derived.functor

end WeilConjectures.PurityFiniteSetting
