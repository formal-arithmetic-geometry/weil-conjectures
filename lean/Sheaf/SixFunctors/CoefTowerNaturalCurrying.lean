/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.SixFunctors.CoefTowerEvaluationPairing
public import Sheaf.Paper.CoefTowerCoaugmentation
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.SixFunctors.FiniteDualizing
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.SixFunctors.FiniteMappingAdjunction
public import Mathlib.Topology.KrullDimension

/-! # Natural currying of the fixed dualizing trace on strict towers

Source: blueprint `prop-coef-integral-dualizing`, proof paragraph 2 and final paragraph,
`main-20261015/sec-smooth-purity/sk-lem-sp-tower`
(blueprint: lem-coef-tower-natural-currying).

Natural-number index n means positive exponent n+1. All tensor products, internal Homs
and equalities retain the strict tower index until explicitly evaluated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalClosed.FunctorCategory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]



/-- The small-Hom localization used by the published point-evaluation functor.
Source: Stacks 079P (blueprint: lem-coef-tower-natural-currying). -/
instance coefCurryingPointDerived :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The coaugmentation dependency uses the standard localization of point modules.
Source: Stacks 0941 (blueprint: lem-coef-tower-natural-currying). -/
abbrev coefCurryingStandardPoint :=
  @DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) _ _
    (HasDerivedCategory.standard _)

/-- Its actual localization functor, before changing the size of Hom types.
Source: Stacks 0941 (blueprint: lem-coef-tower-natural-currying). -/
abbrev coefCurryingStandardPointQ :
    CochainComplex (ModuleCat.{u + 1} (coefTraceRing l E)) ℤ ⥤
      coefCurryingStandardPoint l E :=
  @DerivedCategory.Q (ModuleCat.{u + 1} (coefTraceRing l E)) _ _
    (HasDerivedCategory.standard _)

/-- The canonical localization equivalence from the coaugmentation's standard
point category to the trace's small-Hom category. It identifies the same complexes
and the same fractions; it does not alter the coefficient or module universe.
Source: Stacks 0941, uniqueness of localization
(blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingPointEquivalence :
    coefCurryingStandardPoint l E ≌
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  Localization.uniq (coefCurryingStandardPointQ l E) DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (coefTraceRing l E)) (.up ℤ))

/-- Exact tower evaluation into the coaugmentation's standard point model.
Source: Stacks 0941 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingStandardEvaluate (n : ℕ) :
    coefPairingDerived l E ⥤ coefCurryingStandardPoint l E :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} (coefTraceRing l E))
  ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj (op n)).mapDerivedCategory

/-- The standard evaluation functor is the localization of evaluation on complexes.
Source: Stacks 0941 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingStandardEvaluateFactors (n : ℕ) :
    DerivedCategory.Q ⋙ coefCurryingStandardEvaluate l E n ≅
      (((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj
        (op n)).mapHomologicalComplex (.up ℤ)) ⋙ coefCurryingStandardPointQ l E :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} (coefTraceRing l E))
  ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj
    (op n)).mapDerivedCategoryFactors

/-- Evaluation commutes with the canonical change of localization model.
This is the lift of the identity comparison on evaluated cochain complexes.
Source: Stacks 0941 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingEvaluationTransport (n : ℕ) :
    coefCurryingStandardEvaluate l E n ⋙
        (coefCurryingPointEquivalence l E).functor ≅ coefTraceEvaluation l E n :=
  let V := ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj (op n))
  let Vc := V.mapHomologicalComplex (.up ℤ)
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefPairingModules l E) (.up ℤ))
    _ _ _ _
    (h₁ := ⟨Functor.isoWhiskerRight (coefCurryingStandardEvaluateFactors l E n)
      (coefCurryingPointEquivalence l E).functor⟩)
    (Functor.isoWhiskerLeft Vc
      (Localization.compUniqFunctor (coefCurryingStandardPointQ l E) DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (coefTraceRing l E)) (.up ℤ))))

/-- The actual quotient-module tower, using the recorded quotient-linear maps.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingQuotients : coefPairingModules l E :=
  Functor.ofOpSequence (fun n ↦ coefTraceQuotientMap l E (Nat.le_succ n))



/-- A_bullet in the derived category is the quotient tower concentrated in degree zero.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingTarget : coefPairingDerived l E :=
  (DerivedCategory.singleFunctor (coefPairingModules l E) 0).obj (coefCurryingQuotients l E)



/-- Exact evaluation of A_bullet is the actual quotient module in degree zero.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingTargetEvaluation (n : ℕ) :
    (coefTraceEvaluation l E n).obj (coefCurryingTarget l E) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).obj
        (coefTraceQuotientModule l E n) :=
  (((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj
    (op n)).mapDerivedCategorySingleFunctor.{u + 2, u + 1} 0).app (coefCurryingQuotients l E)



/-- The universal derived tower Hom into the fixed quotient tower. Its evaluation
and bijection specify the right adjoint at that target, uniquely up to the unique
isomorphism preserving evaluation. This is a data interface; it makes no existence
assertion.
Source: blueprint proof paragraph 2; Stacks 08J9
(blueprint: lem-coef-tower-natural-currying). -/
structure CoefCurryingHomModel where
  /-- J, contravariantly functorial in the integral point complex. -/
  hom : (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)))ᵒᵖ ⥤
    coefPairingDerived l E
  /-- The evaluation counit, with the Hom factor first. -/
  evaluation : ∀ C : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)),
    (coefPairingTensor l E).obj
      (hom.obj (op C), (CoefTower.constant (coefTraceRing l E)).obj C) ⟶
        coefCurryingTarget l E
  /-- The right-oriented tensor-Hom bijection. -/
  transpose : ∀ (H : coefPairingDerived l E)
    (C : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))),
    ((coefPairingTensor l E).obj
      (H, (CoefTower.constant (coefTraceRing l E)).obj C) ⟶ coefCurryingTarget l E) ≃
      (H ⟶ hom.obj (op C))
  /-- Its inverse is tensor with the argument followed by evaluation. -/
  transpose_evaluation : ∀ (H : coefPairingDerived l E)
    (C : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)))
    (f : (coefPairingTensor l E).obj
      (H, (CoefTower.constant (coefTraceRing l E)).obj C) ⟶ coefCurryingTarget l E),
    (coefPairingTensor l E).map (Prod.mkHom (transpose H C f) (𝟙 _)) ≫ evaluation C = f
  /-- The contravariant action is the one characterized by evaluation. -/
  evaluation_naturality : ∀
    (C C' : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) (f : C ⟶ C'),
    (coefPairingTensor l E).map (Prod.mkHom (hom.map f.op) (𝟙 _)) ≫ evaluation C =
      (coefPairingTensor l E).map
        (Prod.mkHom (𝟙 _) ((CoefTower.constant (coefTraceRing l E)).map f)) ≫ evaluation C'

/-- The representative Hom complex has at n the ordinary R-linear Hom complex (P,I_n),
with postcomposition by the actual transitions of the simultaneous resolution I.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingHomComplex
    (P : CochainComplex (ModuleCat.{u + 1} (coefTraceRing l E)) ℤ)
    (I : CochainComplex (coefPairingModules l E) ℤ) :
    CochainComplex (coefPairingModules l E) ℤ :=
  coefPairingComplexTower (I.asFunctor ⋙ CochainComplex.internalHom P)

/-- The target of finite evaluation of J is RHom_R(C,A_n), including its
contravariant maps in C.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingPointHom (n : ℕ) :
    (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  MonoidalClosed.internalHom.flip.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).obj
      (coefTraceQuotientModule l E n))

/-- The existing derived tensor in the small-Hom point localization.
Source: Stacks 06YY (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingPointTensor :
    DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) ×
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) ⥤
        DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  MonoidalCategory.tensor _

/-- Point-level evaluation, with Hom first and argument second.
Source: Stacks 08J9 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingPointEvaluation (n : ℕ)
    (C : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
    (coefCurryingPointHom l E n).obj (op C) ⊗ C ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).obj
        (coefTraceQuotientModule l E n) :=
  (DerivedMonoidal.braiding' DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (ModuleCat.{u + 1} (coefTraceRing l E)) (.up ℤ)) _ _).hom ≫ (ihom.ev C).app _

end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The integral compact-support point sections, transported along the canonical
localization equivalence to the very point category used by the trace dependency.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingIntegralSections
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))))) :=
  CoefTower.integralSections D l E T ⋙ (coefCurryingPointEquivalence l E).functor

/-- Finite compact-support point sections in the original standard localization,
with the quotient scalar action of the coaugmentation dependency.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingStandardFiniteSections (n : ℕ) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤ coefCurryingStandardPoint l E :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} (coefTraceRing l E))
  CoefTower.finiteSections D l E (finiteDualizingCompactification D X) n ⋙
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointReductionQuotient l E n)).mapDerivedCategory

/-- The coaugmentation's exact integral point sections in its standard localization.
Source: Stacks 0946 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingStandardIntegralPoint :
    DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ⥤
      coefCurryingStandardPoint l E :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} (coefTraceRing l E))
  (pointIntegralSections l E D.k).mapDerivedCategory

/-- The identity on section complexes, lifted through uniqueness of localization.
Source: Stacks 0941 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingIntegralPointTransport :
    coefCurryingStandardIntegralPoint l E D ⋙ (coefCurryingPointEquivalence l E).functor ≅
      (pointIntegralSections l E D.k).mapDerivedCategory :=
  let V := pointIntegralSections l E D.k
  let Vc := V.mapHomologicalComplex (.up ℤ)
  let standardFactors : DerivedCategory.Q ⋙ coefCurryingStandardIntegralPoint l E D ≅
      Vc ⋙ coefCurryingStandardPointQ l E := by
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} (coefTraceRing l E))
    exact V.mapDerivedCategoryFactors
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (scalarReductionSource.{u, u} l E (Spec (.of D.k)))
      (.up ℤ)) _ _ _ _
    (h₁ := ⟨Functor.isoWhiskerRight standardFactors
      (coefCurryingPointEquivalence l E).functor⟩)
    (Functor.isoWhiskerLeft Vc
      (Localization.compUniqFunctor (coefCurryingStandardPointQ l E) DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (coefTraceRing l E)) (.up ℤ))))

/-- Canonical finite section comparison: identity of quotient and integral section
scalars, followed by the normalized point-section localization comparison. It has
no independent choice of a finite-level automorphism.
Source: Stacks 0946 (blueprint: lem-coef-tower-natural-currying). -/
def coefCurryingFiniteC
    (pointComparison : (pointIntegralSections l E D.k).mapDerivedCategory ≅
      coefPairingIntegralSections l E (Spec (.of D.k))) (n : ℕ) :
    coefCurryingStandardFiniteSections l E D X n ⋙
      (coefCurryingPointEquivalence l E).functor ≅ coefPairingFiniteC l E D X n :=
  Functor.isoWhiskerLeft
    (scalarReductionDerivedExtension l E X n ⋙
      sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
        (Padic.coefficientExtensionRing l E (n + 1)))
    ((Functor.isoWhiskerRight (CoefTower.derivedFiniteSectionsRestriction D l E n)
      (coefCurryingPointEquivalence l E).functor).symm ≪≫
      Functor.isoWhiskerLeft (scalarReductionDerivedRestriction l E (Spec (.of D.k)) n)
        (coefCurryingIntegralPointTransport l E D ≪≫ pointComparison))

/-- Construction witnesses for the already specified pairing and coaugmentation.
This is a data interface; it makes no existence assertion. Comparisons to the
actual compact-support tower and to its finite projections are retained explicitly.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
structure CoefCurryingModels
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (a₀ b₀ : ℤ)
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
    (e : ∀ n : ℕ, T ⋙ pbcTowerEvaluation (Spec (.of D.k))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n ≅
        compactSupportRestrictedLevel l E (finiteDualizingCompactification D X) n) where
  /-- The simultaneous quotient-scalar derived tensor-Hom calculus. -/
  calculus : CoefficientDerivedSystemCalculus l E X
  /-- The actual projection-mate/evaluation pairing. -/
  pairing : CoefPairingSystem l E (finiteDualizingCompactification D X) calculus
  /-- Its ambient finite-level frames, including scalar balancing. -/
  finiteFrame : ∀ n : ℕ,
    CoefPairingFiniteFrame l E (finiteDualizingCompactification D X) calculus pairing n
  /-- Identification with the specified strict compact-support sections tower. -/
  support : coefPairingSupport l E D X calculus ≅ CoefTower.sectionsTower D l E T
  /-- Identity on ordinary sections, with exactly their constant integral action. -/
  pointSections : pointIntegralSections l E D.k ≅
    coefPairingOrdinaryIntegralSections l E (Spec (.of D.k))
  /-- Comparison with separately derived constant scalar restriction and sections. -/
  pointSectionsDerived : (pointIntegralSections l E D.k).mapDerivedCategory ≅
    coefPairingIntegralSections l E (Spec (.of D.k))
  /-- The pairing dependency's fixed identification ev_n B = C_n. -/
  eB : ∀ n : ℕ, coefPairingSupport l E D X calculus ⋙ coefTraceEvaluation l E n ≅
    coefPairingFiniteC l E D X n
  /-- The natural comparison C = Rlim B of the coaugmentation node. -/
  limitComparison : (CoefTower.inputs l E (X := X) a₀ b₀).ι ⋙
      coefCurryingIntegralSections l E D X T ≅
    (CoefTower.inputs l E (X := X) a₀ b₀).ι ⋙ CoefTower.sectionsTower D l E T ⋙
      CoefTower.totalLimit (coefTraceRing l E)
  /-- Scalar adjunction identifies evaluation of the Hom tower with H_n. -/
  finiteHom : ∀ n : ℕ, coefPairingHom l E X calculus Q ⋙ coefTraceEvaluation l E n ≅
    coefPairingFiniteHom l E X n (integralDualizingFiniteTerm l E D X n)
  /-- Evaluation of the compact-support dualizing tower, before its trace. -/
  omegaEvaluation : ∀ n : ℕ,
    (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
      (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).obj
        (integralDualizingFiniteTerm l E D X n)
  /-- Finite comparison to the ordinary-etale exceptional-counit presentation. -/
  omegaOrigin : ∀ n : ℕ,
    (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).obj
      (integralDualizingFiniteTerm l E D X n) ≅ coefTraceFiniteValue l E D X n
  /-- Evaluation of tensor is the K-flat-derived pointwise tensor comparison. -/
  tensorEvaluation : ∀ n : ℕ,
    coefPairingTensor l E ⋙ coefTraceEvaluation l E n ≅
      (coefTraceEvaluation l E n).prod (coefTraceEvaluation l E n) ⋙
        MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)))
  /-- The integral Hom comparison from the pairing dependency. -/
  integralHom : ∀ n : ℕ, coefPairingHom l E X calculus Q ⋙ coefTraceEvaluation l E n ≅
    coefPairingIntegralHom l E X n (integralDualizingFiniteTerm l E D X n)
  /-- The universal derived Hom of constant input into the actual quotient tower. -/
  hom : CoefCurryingHomModel l E
  /-- Evaluation of J is the point Hom, naturally and contravariantly in C. -/
  homEvaluation : ∀ n : ℕ,
    hom.hom ⋙ coefTraceEvaluation l E n ≅ coefCurryingPointHom l E n

variable
  (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
  (a₀ b₀ : ℤ)
  (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
    DerivedCategory (pbcTowers (Spec (.of D.k))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
  (e : ∀ n : ℕ, T ⋙ pbcTowerEvaluation (Spec (.of D.k))
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n ≅
      compactSupportRestrictedLevel l E (finiteDualizingCompactification D X) n)
  (M : CoefCurryingModels l E D X Q a₀ b₀ T e)

/-- The dependency's full pairing clauses and the canonical section normalization,
imposed on the SAME construction witnesses used by gamma and its finite formula.
Source: blueprint paragraph 2; Stacks 0941 and 0946
(blueprint: lem-coef-tower-natural-currying). -/
def CoefCurryingModels.IsSpecified : Prop :=
  /- pointSections_identity: This fixes every component of the comparison. -/
  (∀ (N : scalarReductionSource.{u, u} l E (Spec (.of D.k)))
    (x : (pointIntegralSections l E D.k).obj N), (M.pointSections.hom.app N).hom x = x) ∧
  /- pointSectionsDerived_unit: Exact-localization and derived units fix the comparison.
  Precomposition by Qh is faithful, so no automorphism remains free. -/
  (Functor.whiskerLeft DerivedCategory.Qh M.pointSectionsDerived.hom =
      (pointIntegralSections l E D.k).mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso M.pointSections.symm (.up ℤ)).inv
        DerivedCategory.Qh ≫
      Functor.whiskerLeft
        ((coefTraceConstantScalars l E (Spec (.of D.k))).mapHomotopyCategory (.up ℤ))
        (((sheafSections (ProEt.topology (Spec (.of D.k)))
          (ModuleCat.{u + 1} (coefTraceRing l E))).obj
            (op (ProEt.mk (𝟙 (Spec (.of D.k)))))).rightDerivedFunctorUnit) ≫
      Functor.whiskerRight
        (coefTraceConstantScalars l E (Spec (.of D.k))).mapDerivedCategoryFactorsh.inv
        (((sheafSections (ProEt.topology (Spec (.of D.k)))
          (ModuleCat.{u + 1} (coefTraceRing l E))).obj
            (op (ProEt.mk (𝟙 (Spec (.of D.k)))))).rightDerivedFunctor)) ∧
  /- support_finite: The M.support comparison is pinned against M.eB and finiteEvaluation. -/
  (∀ n : ℕ,
    (Functor.isoWhiskerRight M.support (coefTraceEvaluation l E n) ≪≫
      Functor.isoWhiskerLeft (CoefTower.sectionsTower D l E T)
        (coefCurryingEvaluationTransport l E n).symm ≪≫
      Functor.isoWhiskerRight
        (CoefTower.finiteEvaluation D l E (finiteDualizingCompactification D X) T e n)
        (coefCurryingPointEquivalence l E).functor ≪≫
      coefCurryingFiniteC l E D X M.pointSectionsDerived n).hom = (M.eB n).hom) ∧
  /- pairingHomComplex: The simultaneous Hom-complex computation of the M.pairing dependency. -/
  (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
    (_eP : DerivedCategory.Q.obj P ≅ K)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E X) ℤ)
    (_hI : I.IsKInjective)
    (_eI : DerivedCategory.Q.obj I ≅
      (coefficientSequenceDerivedRestriction.{u, u} l E X).obj (coefTraceInput l E X Q)),
    Nonempty ((coefPairingHom l E X M.calculus Q).obj (op K) ≅
      DerivedCategory.Q.obj (coefPairingHomComplex l E X P I))) ∧
  /- integralHom_scalar: The same eH factors through integral-to-finite scalar adjunction. -/
  (∀ n : ℕ, ∃ scalarIso :
    coefPairingIntegralHom l E X n (integralDualizingFiniteTerm l E D X n) ≅
      coefPairingFiniteHom l E X n (integralDualizingFiniteTerm l E D X n),
    (M.integralHom n).hom ≫ scalarIso.hom = (M.finiteHom n).hom) ∧
  /- pairingTransitions: Every quotient transition is the prescribed map. -/
  (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    {m n : ℕ} (h : n ≤ m),
    (coefTraceTransition l E h).app ((coefPairingSupport l E D X M.calculus).obj K) ≫
      (M.eB n).hom.app K = (M.eB m).hom.app K ≫
        (coefPairingIntegralSections l E (Spec (.of D.k))).map
          (compactSupportRestrictedTransition l E (finiteDualizingCompactification D X)
            m n h K)) ∧
  /- pairingEvaluation: Beta uses these very tensor, Hom, M.support and omega comparisons. -/
  (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
    finiteTorConstructibleIntegral l E X K → ∀ n : ℕ,
    (coefTraceEvaluation l E n).map
        (M.pairing.beta l E (M.calculus.reduction.obj K) (coefTraceInput l E X Q)) ≫
        (M.omegaEvaluation n).hom =
      (M.tensorEvaluation n).hom.app
        ((coefPairingHom l E X M.calculus Q).obj (op K),
          (coefPairingSupport l E D X M.calculus).obj K) ≫
        ((M.finiteHom n).hom.app (op K) ⊗ₘ (M.eB n).hom.app K) ≫
          coefPairingFiniteBeta l E (finiteDualizingCompactification D X)
            M.calculus M.pairing n (M.finiteFrame n)
            ((scalarReductionDerivedExtension l E X n).obj K)
            (integralDualizingFiniteTerm l E D X n)) ∧
  /- pairingDinaturality: Dinaturality holds before evaluating the tower index. -/
  (∀ (K K' : DerivedCategory (scalarReductionSource.{u, u} l E X)),
    finiteTorConstructibleIntegral l E X K → finiteTorConstructibleIntegral l E X K' →
    ∀ f : K ⟶ K',
    (coefPairingTensor l E).map
        (Prod.mkHom ((coefPairingHom l E X M.calculus Q).map f.op) (𝟙 _)) ≫
        M.pairing.beta l E (M.calculus.reduction.obj K) (coefTraceInput l E X Q) =
      (coefPairingTensor l E).map
        (Prod.mkHom (𝟙 _) ((coefPairingSupport l E D X M.calculus).map f)) ≫
        M.pairing.beta l E (M.calculus.reduction.obj K') (coefTraceInput l E X Q))

/-- The coaugmentation is exactly the derived constant/limit counit, transported
through the compact-support comparison supplied by the pairing construction.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def CoefCurryingModels.eta :
    (CoefTower.inputs l E (X := X) a₀ b₀).ι ⋙ coefCurryingIntegralSections l E D X T ⋙
        CoefTower.constant (coefTraceRing l E) ⟶
      (CoefTower.inputs l E (X := X) a₀ b₀).ι ⋙ coefPairingSupport l E D X M.calculus :=
  Functor.whiskerRight M.limitComparison.hom (CoefTower.constant (coefTraceRing l E)) ≫
    Functor.whiskerLeft
      ((CoefTower.inputs l E (X := X) a₀ b₀).ι ⋙ CoefTower.sectionsTower D l E T)
      (CoefTower.adjunction (coefTraceRing l E)).counit ≫
    Functor.whiskerLeft (CoefTower.inputs l E (X := X) a₀ b₀).ι M.support.inv

/-- The finite evaluation of B uses its actual strict-tower evaluation comparison.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def CoefCurryingModels.supportEvaluation (n : ℕ) :
    coefPairingSupport l E D X M.calculus ⋙ coefTraceEvaluation l E n ≅
      coefPairingFiniteC l E D X n :=
  M.eB n

/-- The actual compact-support projection q_n, with its finite sections comparison.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def CoefCurryingModels.finiteProjection (n : ℕ)
    (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory) :
    (coefCurryingIntegralSections l E D X T).obj K.obj ⟶
      (coefPairingFiniteC l E D X n).obj K.obj :=
  (coefCurryingPointEquivalence l E).functor.map
    ((CoefTower.compactSupportProjection D l E
      (finiteDualizingCompactification D X) T e n).app K.obj) ≫
      (coefCurryingFiniteC l E D X M.pointSectionsDerived n).hom.app K.obj

/-- The canonical finite gamma followed by scalar adjunction, specified by its
normalized transpose: projection q_n in the second variable, scalar balancing,
compact-support projection and evaluation, then the finite exceptional counit.
This is the evaluation characterization of finiteMappingAdjunction and of the
scalar-adjunction node; it does not select an arbitrary isomorphism of endpoints.
Source: blueprint proof paragraph 2, third comparison; Stacks 08J9 and 07A6
(blueprint: lem-coef-tower-natural-currying). -/
def CoefCurryingModels.finiteArrow (n : ℕ)
    (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory) :
    (coefPairingFiniteHom l E X n (integralDualizingFiniteTerm l E D X n)).obj (op K.obj) ⟶
      (coefCurryingPointHom l E n).obj
        (op ((coefCurryingIntegralSections l E D X T).obj K.obj)) :=
  MonoidalClosed.curry
    ((DerivedMonoidal.braiding' DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (ModuleCat.{u + 1} (coefTraceRing l E)) (.up ℤ)) _ _).hom ≫
      (coefCurryingPointTensor l E).map
        (Prod.mkHom (𝟙 ((coefPairingFiniteHom l E X n
          (integralDualizingFiniteTerm l E D X n)).obj (op K.obj)))
          (M.finiteProjection l E D X Q a₀ b₀ T e n K)) ≫
      coefPairingFiniteBeta l E (finiteDualizingCompactification D X) M.calculus M.pairing
        n (M.finiteFrame n) ((scalarReductionDerivedExtension l E X n).obj K.obj)
        (integralDualizingFiniteTerm l E D X n) ≫
      (M.omegaOrigin n).hom ≫ coefTraceFiniteCounit l E D X n ≫
        (coefTraceTargetIso l E D n).hom)

/-- The required arrow is a defined transpose in the derived tower category itself.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-natural-currying). -/
def CoefCurryingModels.gamma
    (t : coefTraceDualizingTower l E D X Q ⟶ coefCurryingTarget l E)
    (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory) :
    (coefPairingHom l E X M.calculus Q).obj (op K.obj) ⟶
      (M.hom.hom).obj (op ((coefCurryingIntegralSections l E D X T).obj K.obj)) :=
  M.hom.transpose _ _
    ((coefPairingTensor l E).map
      (Prod.mkHom (𝟙 _) ((M.eta l E D X Q a₀ b₀ T e).app K)) ≫
        M.pairing.beta l E (M.calculus.reduction.obj K.obj) (coefTraceInput l E X Q) ≫ t)

end WeilConjectures

/- The former `coefTowerNaturalCurrying` theorem is withdrawn: its arbitrary
`eTrace` did not preserve the dualizing counit and allowed degenerate pairings.
The coherent comparison used by the current route is stated separately in
`IntegralDualizingMappingTowerFiniteComparison`. The definitions above remain
available for the strict tower constructions and finite-adjunction interfaces. -/
