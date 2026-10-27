/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
public import Sheaf.Paper.IntegralOperationsScalarComparisons
import all Sheaf.Paper.PointQuotientAugmentationDiagram
import all Sheaf.Paper.IntegralOperationsWellDefined
import all Sheaf.Paper.IntegralStalkRoosControl
import Sheaf.Paper.ExactFunctorGoodTruncations
import Sheaf.Paper.IntegralQuotientCohomologicalBounds
import Sheaf.Paper.QuotientGermTower

/-!
# Bounded quotient towers and completed geometric stalks

Source: Stacks Project, Tags 0118, 0993, 05V1 and 0941; blueprint
`thm-trf-l-function-euler-product`, Step 1, Local powers (b)
(blueprint: lem-trf-bounded-quotient-stalk-realization).

The positive exponent is indexed by `n + 1`. All products, quotient transitions,
truncations and cone maps are the published constructions, before localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Keep the sheaf-of-modules abelian structure on `integralTowerModules`: since
-- `QcqsCompactSupportRealization` publicly imports `QcqsCompactSupportStrictReductionComparison`,
-- `SemilinearSections.moduleAbelian` is visible here and its site bound leaves a free universe.
attribute [local instance 5000] SheafOfModules.instAbelian

/-- Upper good truncation of a strict tower, using induced maps on kernels.
Source: Stacks 0118 (blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfUpperTower {A : Type a} [Category.{b} A] [Abelian A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) :=
  C ⋙ (ComplexShape.embeddingUpIntLE q).truncLEFunctor A

/-- The strict bounded tower; at coinciding boundaries the term is cohomology.
Source: Stacks 0118 (blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfBoundedTower {A : Type a} [Category.{b} A] [Abelian A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p q : ℤ) :=
  trfUpperTower C q ⋙ (ComplexShape.embeddingUpIntGE p).truncGEFunctor A

/-- The upper arrow is a strict tower map, natural in the input tower.
Source: Stacks 0118 (blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfUpperArrow {A : Type a} [Category.{b} A] [Abelian A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) : trfUpperTower C q ⟶ C :=
  Functor.whiskerLeft C ((ComplexShape.embeddingUpIntLE q).ιTruncLENatTrans A)

/-- The lower arrow is induced by the cokernel projection, at every tower level.
Source: Stacks 0118 (blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfLowerArrow {A : Type a} [Category.{b} A] [Abelian A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p q : ℤ) :
    trfUpperTower C q ⟶ trfBoundedTower C p q :=
  Functor.whiskerLeft (trfUpperTower C q)
    ((ComplexShape.embeddingUpIntGE p).πTruncGENatTrans A)

/-- The claimed bounded zigzag, with genuine good truncations, not replacement objects.
Source: Stacks 0118 (blueprint: lem-trf-bounded-quotient-stalk-realization). -/
abbrev TrfBoundedZigzag {A : Type a} [Category.{b} A] [Abelian A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p q : ℤ) : Prop :=
  (∀ n : ℕ, QuasiIso ((trfUpperArrow C q).app (op n)) ∧
    QuasiIso ((trfLowerArrow C p q).app (op n))) ∧
  (∀ (n : ℕ) (i : ℤ), i < p ∨ q < i →
    IsZero (((trfBoundedTower C p q).obj (op n)).X i)) ∧
  (p = q → ∀ n : ℕ,
    Nonempty ((((trfBoundedTower C p q).obj (op n)).X p) ≅
      (C.obj (op n)).homology p))

/-- Pullback compatibility includes naturality for every complex map and the two
canonical boundary arrows; whiskering gives compatibility with every strict tower.
Source: Stacks 0118, 05V1
(blueprint: lem-trf-bounded-quotient-stalk-realization). -/
abbrev TrfTruncationCompatible {A : Type a} [Category.{b} A] [Abelian A]
    {B : Type c} [Category.{d} B] [Abelian B] (F : A ⥤ B) [F.Additive]
    (p q : ℤ) : Prop :=
  ∃ (e : (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙
        F.mapHomologicalComplex (.up ℤ) ≅ F.mapHomologicalComplex (.up ℤ) ⋙
          (ComplexShape.embeddingUpIntLE q).truncLEFunctor B)
    (f : (ComplexShape.embeddingUpIntGE p).truncGEFunctor A ⋙
        F.mapHomologicalComplex (.up ℤ) ≅ F.mapHomologicalComplex (.up ℤ) ⋙
          (ComplexShape.embeddingUpIntGE p).truncGEFunctor B),
    (∀ K : CochainComplex A ℤ,
      e.hom.app K ≫ CochainComplex.ιTruncLE
          ((F.mapHomologicalComplex (.up ℤ)).obj K) q =
        (F.mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE q)) ∧
    (∀ K : CochainComplex A ℤ,
      (F.mapHomologicalComplex (.up ℤ)).map (K.πTruncGE p) ≫ f.hom.app K =
        CochainComplex.πTruncGE ((F.mapHomologicalComplex (.up ℤ)).obj K) p)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual quotient tower, functorial in all chain maps, with completed scalars.
Source: Stacks 06YY (blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfQuotientTower (T : Scheme.{u}) :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E T n)
    (unrestrictedIntegralTransition l E T)).flip

/-- Apply the canonical integral stalk, including its constant-scalar action, levelwise.
Source: Stacks 0993 (blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfQuotientStalkTower {T : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    (v : Spec (.of k) ⟶ T) :=
  trfQuotientTower l E T ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      ((integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ))

/-- Exact point sections of the strict finite pullback tower, with their integral action.
Source: Stacks 05V1, 0941
(blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfQuotientSectionTower {T : Scheme.{u}} {k : Type u} [Field k]
    (v : Spec (.of k) ⟶ T) :=
  integralOperationsPullbackTowerFunctor l E v ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      ((pointIntegralSections l E k).mapHomologicalComplex (.up ℤ))

/-- The ambient derived integral point fibre `J_v`; on constructible inputs this is
exactly the underlying object of the recorded `pointIntegralFibre`.
Source: blueprint order 1509; Stacks 0941
(blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfCompletedPointFibre (D : FiniteFieldDatum.{u}) {T : Scheme.{u}}
    (v : Spec (.of D.k) ⟶ T) :=
  integralDerivedPullback l E v ⋙ pointFibreIntegralAmbient D l E

/-- The published small-Hom localization of integral coefficient modules.
Source: blueprint order 1509
(blueprint: lem-trf-bounded-quotient-stalk-realization). -/
abbrev trfIntegralModuleQ :=
  @DerivedCategory.Q
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- Exact sections with the localization dictionaries used by the point fibre.
Source: blueprint order 1509
(blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfIntegralSectionsFactors (D : FiniteFieldDatum.{u}) :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointIntegralSections l E D.k) _ _ _

/-- The prescribed arrow uses the defining pullback comparison and the canonical
sectionwise product map on both coordinates, followed by the diagonal germ map.
There is no choice of a map completing a triangle.
Source: Stacks 0993, 05V1, 0941
(blueprint: lem-trf-bounded-quotient-stalk-realization). -/
def trfQuotientStalkRealizationArrow (D : FiniteFieldDatum.{u}) {T : Scheme.{u}}
    (v : Spec (.of D.k) ⟶ T)
    (e : trfQuotientSectionTower l E v ≅ trfQuotientStalkTower l E v)
    (M : DerivedCategory (integralTowerModules l E T))
    (P : (integralOperationsGoodComplex l E T).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ M) :
    (trfCompletedPointFibre l E D v).obj M ⟶
      (trfIntegralModuleQ l E).obj (integralOperationsRoos
        ((trfQuotientStalkTower l E v).obj P.obj)) :=
  (pointFibreIntegralAmbient D l E).map
      ((integralDerivedPullback l E v).map q.inv ≫
        (integralDerivedPullbackComparison l E v).hom.app P) ≫
    (trfIntegralSectionsFactors l E D).hom.app
      ((integralOperationsPullbackComplexFunctor l E v).obj P.obj) ≫
    (trfIntegralModuleQ l E).map
      (scalarRoosMap (pointIntegralSections l E D.k)
        ((integralOperationsPullbackTowerFunctor l E v).obj P.obj) ≫
          integralOperationsRoosMap (e.hom.app P.obj))

/-- Finite coefficients at the point: the identity stalk is sections, and the
pullback comparison is prescribed on every pullback-unit germ. The last clause
identifies the complete strict tower map, before localization, with those maps.
Source: Stacks 0993 and 05V1
(blueprint: lem-trf-bounded-quotient-stalk-realization). -/
abbrev TrfQuotientGermNormalized (D : FiniteFieldDatum.{u}) {T : Scheme.{u}}
    (v : Spec (.of D.k) ⟶ T)
    (γ : ∀ n : ℕ, pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
      finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of D.k)))
        (Padic.coefficientExtensionRing l E (n + 1)))
    (δ : ∀ n : ℕ, integralOperationsLevelPullback l E v n ⋙
      pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
        finiteCoefficientModuleStalkFunctor v (Padic.coefficientExtensionRing l E (n + 1)))
    (e : trfQuotientSectionTower l E v ≅ trfQuotientStalkTower l E v) : Prop :=
  (∀ (n : ℕ) (F : integralOperationsFiniteModules l E (Spec (.of D.k)) n)
      (x : F.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
    (γ n).hom.app F x =
      proEtaleCoefficientModuleGerm (𝟙 (Spec (.of D.k)))
        (Padic.coefficientExtensionRing l E (n + 1)) F
          (proEtaleConstantGermNeighbourhood (𝟙 (Spec (.of D.k)))) x) ∧
  (∀ (n : ℕ) (F : integralOperationsFiniteModules l E T n)
      (N : ProEtaleGeometricNeighbourhood v)
      (θ : ProEt.mk (𝟙 (Spec (.of D.k))) ⟶ (proEtaleBaseChange v).obj N.right)
      (x : F.val.obj (op N.right)),
    θ.left ≫ pullback.fst N.right.hom v = N.hom.left →
      (δ n).hom.app F
        (((integralOperationsLevelPullback l E v n).obj F).val.map θ.op
          (integralOperationsPullbackGenerator l E v n F N.right x)) =
        proEtaleCoefficientModuleGerm v (Padic.coefficientExtensionRing l E (n + 1)) F N x) ∧
  (∀ (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) (i : ℤ)
      (x : (((trfQuotientSectionTower l E v).obj P).obj (op n)).X i),
    (((e.hom.app P).app (op n)).f i) x =
      (δ n).hom.app (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) x)

/-- All clauses of the bounded quotient-stalk realization. The interval is a
cohomological bound, not a bound on terms or on Tor amplitude. Good truncations
are explicit tower functors; the comparison is fixed on both cone coordinates.
Naturality is stated for arbitrary derived maps and every compatible chain map.
Inverting a quasi-isomorphism in this equation gives the same equation for its
inverse, and composition gives the equation for every roof.
Source: Stacks 0118, 0993, 05V1, 0941
(blueprint: lem-trf-bounded-quotient-stalk-realization). -/
abbrev TrfBoundedQuotientStalkRealized (D : FiniteFieldDatum.{u}) {T : Scheme.{u}}
    (v : Spec (.of D.k) ⟶ T) : Prop :=
  ∃ (γ : ∀ n : ℕ, pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
      finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of D.k)))
        (Padic.coefficientExtensionRing l E (n + 1)))
    (δ : ∀ n : ℕ, integralOperationsLevelPullback l E v n ⋙
      pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
        finiteCoefficientModuleStalkFunctor v (Padic.coefficientExtensionRing l E (n + 1)))
    (e : trfQuotientSectionTower l E v ≅ trfQuotientStalkTower l E v),
    TrfQuotientGermNormalized l E D v γ δ e ∧
    (∀ (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
      (f : X ⟶ T) (n : ℕ) (p q : ℤ),
      TrfTruncationCompatible (integralOperationsLevelPullback l E f n) p q) ∧
    (∀ (M : DerivedCategory (integralTowerModules l E T)), sfIntegralConstructible l E T M →
      ∀ (P : (integralOperationsGoodComplex l E T).FullSubcategory)
        (q : DerivedCategory.Q.obj P.obj ≅ M),
      (∃ p r : ℤ, p ≤ r ∧ ∀ n : ℕ,
        CochainComplex.IsGE (((trfQuotientTower l E T).obj P.obj).obj (op n)) p ∧
          CochainComplex.IsLE (((trfQuotientTower l E T).obj P.obj).obj (op n)) r) ∧
      (∀ (p r : ℤ), p ≤ r →
        (∀ n : ℕ, CochainComplex.IsGE (((trfQuotientTower l E T).obj P.obj).obj (op n)) p ∧
          CochainComplex.IsLE (((trfQuotientTower l E T).obj P.obj).obj (op n)) r) →
        TrfBoundedZigzag ((trfQuotientTower l E T).obj P.obj) p r ∧
        QuasiIso (integralOperationsRoosMap
          (Functor.whiskerRight (trfUpperArrow ((trfQuotientTower l E T).obj P.obj) r)
            ((integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ)))) ∧
        QuasiIso (integralOperationsRoosMap
          (Functor.whiskerRight (trfLowerArrow ((trfQuotientTower l E T).obj P.obj) p r)
            ((integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ))))) ∧
      IsIso (scalarRoosMap (pointIntegralSections l E D.k)
        ((integralOperationsPullbackTowerFunctor l E v).obj P.obj)) ∧
      ∃ ε : (trfCompletedPointFibre l E D v).obj M ≅
        (trfIntegralModuleQ l E).obj
          (integralOperationsRoos ((trfQuotientStalkTower l E v).obj P.obj)),
        ε.hom = trfQuotientStalkRealizationArrow l E D v e M P q) ∧
    (∀ (M M' : DerivedCategory (integralTowerModules l E T))
      (_hM : sfIntegralConstructible l E T M) (_hM' : sfIntegralConstructible l E T M')
      (P P' : (integralOperationsGoodComplex l E T).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ M) (q' : DerivedCategory.Q.obj P'.obj ≅ M')
      (w : P.obj ⟶ P'.obj) (h : M ⟶ M'),
      DerivedCategory.Q.map w ≫ q'.hom = q.hom ≫ h →
      (trfCompletedPointFibre l E D v).map h ≫
          trfQuotientStalkRealizationArrow l E D v e M' P' q' =
        trfQuotientStalkRealizationArrow l E D v e M P q ≫
          (trfIntegralModuleQ l E).map
            (integralOperationsRoosMap ((trfQuotientStalkTower l E v).map w)))

set_option backward.isDefEq.respectTransparency true

private local instance trfModuleLimits (R : Type (u + 1)) [Ring R] :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
  @ModuleCat.hasLimits'.{u + 1} R inferInstance

attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  CategoryTheory.Limits.limit CategoryTheory.constantSheaf DerivedCategory.Q
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  pointIntegralSections PointQuotientAugmentation.roosComparison
  integralOperationsRoosMap

private theorem trfBoundedZigzag_of_bounds
    {A : Type a} [Category.{b} A] [Abelian A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p r : ℤ)
    (h : ∀ n : ℕ, CochainComplex.IsGE (C.obj (op n)) p ∧
      CochainComplex.IsLE (C.obj (op n)) r) : TrfBoundedZigzag C p r := by
  have hu (n : ℕ) : QuasiIso ((trfUpperArrow C r).app (op n)) := by
    change QuasiIso ((C.obj (op n)).ιTruncLE r)
    exact (CochainComplex.quasiIso_ιTruncLE_iff _ _).2 (h n).2
  have hl (n : ℕ) : QuasiIso ((trfLowerArrow C p r).app (op n)) := by
    have : QuasiIso ((C.obj (op n)).ιTruncLE r) := hu n
    have hge : CochainComplex.IsGE ((C.obj (op n)).truncLE r) p :=
      (HomologicalComplex.isSupported_iff_of_quasiIso
        ((C.obj (op n)).ιTruncLE r) (ComplexShape.embeddingUpIntGE p)).2 (h n).1
    change QuasiIso (((C.obj (op n)).truncLE r).πTruncGE p)
    exact (CochainComplex.quasiIso_πTruncGE_iff _ _).2 hge
  refine ⟨fun n ↦ ⟨hu n, hl n⟩, ?_, ?_⟩
  · intro n i hi
    change IsZero ((((C.obj (op n)).truncLE r).truncGE p).X i)
    rcases hi with hi | hi
    · exact CochainComplex.isZero_of_isStrictlyGE _ p i hi
    · exact CochainComplex.isZero_of_isStrictlyLE _ r i hi
  · intro hpr n
    subst r
    let K := C.obj (op n)
    have : QuasiIso (K.ιTruncLE p) := hu n
    have hd : (K.truncLE p).d p (p + 1) = 0 :=
      (CochainComplex.isZero_of_isStrictlyLE (K.truncLE p) p (p + 1)
        (by omega)).eq_of_tgt _ _
    change Nonempty (((K.truncLE p).truncGE p).X p ≅ K.homology p)
    exact ⟨(K.truncLE p).truncGEXIsoOpcycles p ≪≫
      ((K.truncLE p).isoHomologyι p (p + 1) (by simp) hd).symm ≪≫
      isoOfQuasiIsoAt (K.ιTruncLE p) p⟩

private theorem trfStalkRoosZigzag (D : FiniteFieldDatum.{u}) {T : Scheme.{u}}
    (v : Spec (.of D.k) ⟶ T)
    (C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) (p r : ℤ)
    (h : TrfBoundedZigzag C p r) :
    QuasiIso (integralOperationsRoosMap
      (A := ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))
      (Functor.whiskerRight (trfUpperArrow C r)
        ((integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ)))) ∧
    QuasiIso (integralOperationsRoosMap
      (A := ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))
      (Functor.whiskerRight (trfLowerArrow C p r)
        ((integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ)))) := by
  let F := integralCoefficientModuleStalkFunctor l E v
  have : PreservesFiniteLimits F := (stalk_exact_products l E v).1
  have : PreservesFiniteColimits F := (stalk_exact_products l E v).2.1
  constructor
  · refine @roosMap_quasiIso.{u + 2, u + 1, u + 2} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _ _
      (HasDerivedCategory.standard.{u + 1, u + 2} (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
      (inferInstance : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))) _ _ _ ?_
    intro n
    have := (h.1 n).1
    change QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      ((trfUpperArrow C r).app (op n)))
    infer_instance
  · refine @roosMap_quasiIso.{u + 2, u + 1, u + 2} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _ _
      (HasDerivedCategory.standard.{u + 1, u + 2} (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
      (inferInstance : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))) _ _ _ ?_
    intro n
    have := (h.1 n).2
    change QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      ((trfLowerArrow C p r).app (op n)))
    infer_instance

private theorem trfScalarRoos_eq
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    scalarRoosMap F C = (PointQuotientAugmentation.roosComparison F).hom.app C := by
  apply ((scalarRoosMap_existsUnique F C).unique ?_
    (scalarRoosMap_existsUnique F C).exists.choose_spec).symm
  have h := PointQuotientAugmentation.roosComparison_coordinates F
  constructor
  · intro n
    apply HomologicalComplex.hom_ext
    intro i
    exact h.1 C n i
  · intro i j hij n
    subst j
    exact h.2 C n i

private theorem trfRoosFunctor_map
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : C ⟶ C') :
    integralOperationsRoosFunctor.map α = integralOperationsRoosMap α := rfl

private theorem trfRepresentative_naturality
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] (L : A ⥤ B) (F : B ⥤ C) (G : A ⥤ C)
    (η : L ⋙ F ⟶ G) {P P' : A} {M M' : B}
    (q : L.obj P ≅ M) (q' : L.obj P' ≅ M') (w : P ⟶ P') (h : M ⟶ M')
    (hw : L.map w ≫ q'.hom = q.hom ≫ h) :
    F.map h ≫ (F.map q'.inv ≫ η.app P') =
      (F.map q.inv ≫ η.app P) ≫ G.map w := by
  have heq : h ≫ q'.inv = q.inv ≫ L.map w := by
    apply (cancel_epi q.hom).1
    rw [← Category.assoc, ← hw]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← F.map_comp, heq, F.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun t ↦ F.map q.inv ≫ t) (η.naturality w)

private theorem trfChain_naturality
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] (L : A ⥤ B) (F : B ⥤ C)
    {G₁ G₂ G₃ : A ⥤ C}
    (a : L ⋙ F ⟶ G₁) (b : G₁ ⟶ G₂) (c : G₂ ⟶ G₃)
    {P P' : A} {M M' : B}
    (q : L.obj P ≅ M) (q' : L.obj P' ≅ M') (w : P ⟶ P') (h : M ⟶ M')
    (hw : L.map w ≫ q'.hom = q.hom ≫ h) :
    F.map h ≫ F.map q'.inv ≫ a.app P' ≫ b.app P' ≫ c.app P' =
      F.map q.inv ≫ a.app P ≫ b.app P ≫ c.app P ≫ G₃.map w := by
  simpa only [NatTrans.comp_app, Category.assoc] using
    trfRepresentative_naturality L F G₃ (a ≫ b ≫ c) q q' w h hw

/-- Uniform bounded quotient towers and the specified completed geometric stalk realization.
Source: Stacks 0118 (truncations), 0993 (classical point), 05V1 (pullback stalks),
0941 (strict derived limits); blueprint Euler-product proof, Local powers (b)
(blueprint: lem-trf-bounded-quotient-stalk-realization).

Proof:
1. quotientGermTower supplies the normalized finite comparisons and their strict
   natural tower isomorphism. Exact finite pullback commutes with the two good
   truncations by exactFunctorGoodTruncations, including the canonical arrows.
2. integralQuotientCohomologicalBounds transports the uniform constructible
   interval to every actual quotient complex of the chosen good representative.
   Mathlib's truncation quasi-isomorphism criteria give both zigzag arrows.
   Strict support gives the zero terms, and at equal boundaries the opcycles of
   the upper truncation identify the retained term with the original homology.
3. stalk_exact_products makes the integral stalk exact. It therefore preserves
   both levelwise quasi-isomorphisms. roosMap_quasiIso then gives precisely the
   two displayed Roos quasi-isomorphisms, using exact products of modules.
4. Exact point sections preserve countable products. Their explicit natural
   Roos comparison has the same two coordinates as scalarRoosMap, so uniqueness
   identifies these maps and makes scalarRoosMap an isomorphism.
5. Each factor of the prescribed arrow is invertible: the good-representative
   pullback comparison transported along q inverse, the derived sections
   factorization, the Roos comparison, and the image of the germ tower map.
   Take the isomorphism whose hom is this exact arrow.
6. Naturality of this composite and the equation for w and h prove the displayed
   derived naturality equality by cancelling q and q prime. No representative
   choice or change of the specified comparison arrow is needed. -/
theorem trfBoundedQuotientStalkRealization (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)]
    (v : Spec (.of D.k) ⟶ T) : TrfBoundedQuotientStalkRealized l E D v := by
  have _hl := hl
  obtain ⟨γ, δ, e, he⟩ := quotientGermTower l E D v
  refine ⟨γ, δ, e, he, ?_, ?_, ?_⟩
  · intro X _ f n p r
    have : PreservesFiniteLimits (integralOperationsLevelPullback.{u, u} l E f n) :=
      (coefficientProEtaleModulePullback_exact.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).1
    have : PreservesFiniteColimits (integralOperationsLevelPullback.{u, u} l E f n) :=
      (coefficientProEtaleModulePullback_exact.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).2
    exact exactFunctorGoodTruncations (integralOperationsLevelPullback.{u, u} l E f n) p r
  · intro M hM P q
    refine ⟨integralQuotientCohomologicalBounds l E T M hM P q, ?_, ?_, ?_⟩
    · intro p r _ hbound
      have hz := trfBoundedZigzag_of_bounds ((trfQuotientTower l E T).obj P.obj) p r hbound
      exact ⟨hz, trfStalkRoosZigzag l E D v _ p r hz⟩
    · have := PointQuotientAugmentation.sectionsProducts l E D.k
      rw [trfScalarRoos_eq]
      exact NatIso.hom_app_isIso
        (PointQuotientAugmentation.roosComparison
          (pointIntegralSections l E D.k)) _
    · have := PointQuotientAugmentation.sectionsProducts l E D.k
      have hscalar : IsIso (scalarRoosMap (pointIntegralSections l E D.k)
          ((integralOperationsPullbackTowerFunctor l E v).obj P.obj)) := by
        rw [trfScalarRoos_eq]
        exact NatIso.hom_app_isIso
          (PointQuotientAugmentation.roosComparison
            (pointIntegralSections l E D.k)) _
      refine ⟨(pointFibreIntegralAmbient D l E).mapIso
          ((integralDerivedPullback l E v).mapIso q.symm ≪≫
            (integralDerivedPullbackComparison l E v).app P) ≪≫
        (trfIntegralSectionsFactors l E D).app
          ((integralOperationsPullbackComplexFunctor l E v).obj P.obj) ≪≫
        (trfIntegralModuleQ l E).mapIso
          (@asIso _ _ _ _ (scalarRoosMap (pointIntegralSections l E D.k)
              ((integralOperationsPullbackTowerFunctor l E v).obj P.obj)) hscalar ≪≫
            integralOperationsRoosFunctor.mapIso (e.app P.obj)), ?_⟩
      rfl
  · intro M M' _ _ P P' q q' w h hw
    have := PointQuotientAugmentation.sectionsProducts l E D.k
    have hn := trfChain_naturality
      (integralOperationsGoodLocalization.{u, u} l E T) (trfCompletedPointFibre l E D v)
      (Functor.whiskerRight (integralDerivedPullbackComparison.{u, u} l E v).hom
        (pointFibreIntegralAmbient D l E))
      (Functor.whiskerLeft
        ((integralOperationsGoodComplex.{u, u} l E T).ι ⋙
          integralOperationsPullbackComplexFunctor.{u, u} l E v)
        (trfIntegralSectionsFactors l E D).hom)
      (Functor.whiskerRight
        (Functor.whiskerLeft
            ((integralOperationsGoodComplex.{u, u} l E T).ι ⋙
              integralOperationsPullbackTowerFunctor.{u, u} l E v)
            (PointQuotientAugmentation.roosComparison (pointIntegralSections l E D.k)).hom ≫
          Functor.whiskerRight
            (Functor.whiskerLeft (integralOperationsGoodComplex.{u, u} l E T).ι e.hom)
            integralOperationsRoosFunctor)
        (trfIntegralModuleQ l E))
      q q' (ObjectProperty.homMk w) h hw
    dsimp only [trfQuotientStalkRealizationArrow, trfCompletedPointFibre,
      Functor.comp_map]
    rw [trfScalarRoos_eq, trfScalarRoos_eq]
    dsimp only [Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, trfCompletedPointFibre, Functor.comp_map,
      Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map] at hn
    simp only [(pointFibreIntegralAmbient D l E).map_comp,
      Category.assoc, trfRoosFunctor_map] at hn ⊢
    dsimp only [ObjectProperty.homMk] at hn
    exact hn

end WeilConjectures
