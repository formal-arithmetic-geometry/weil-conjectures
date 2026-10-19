/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.IntegralReductionTower
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.CategoryTheory.ClosedAdjunctionComparison
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.TensorParameterComposition
/-! # Coherent derived coefficient-system evaluation

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 0A95 and 0941;
Injectives, Tag 079P (blueprint: lem-coef-derived-system-evaluation-calculus).
The natural number n denotes the positive coefficient exponent n+1.

## Main definitions

- `CoefficientFiniteTensorNormalization`: canonical scalar tensor comparison on K-flats.
- `CoefficientReductionTensorNormalization`: the strict representative reduction tensor map.
- `CoefficientDerivedSystemCalculus`: reduction, adjunction, fiber Hom and enriched comparison.
- `CoefficientDerivedSystemCoherence`: simultaneous resolution and projection identities.
- `coefficientGammaZeroMap`: H⁰ of gamma followed by the actual fiber projection.

## Main statements

- `coefficientDerivedSystemEvaluationCalculus`: existence of the calculus and its coherence.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Use coefficient-universe sheafification: the generic instance requires a successor.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v a b r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Derived termwise global sections, keeping the strict tower until after deriving.
Source: Stacks 079P, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientTowerSections :
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) :=
  (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource l E W)
    AddCommGrpCat.{max u (t+1)}).obj
      (preadditiveCoyoneda.obj (op (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E W))))

/-- Global sections on towers are additive, component by component.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: at every level, Hom from the module unit preserves addition of maps.
Natural transformations are equal when all components are equal. -/
theorem coefficientTowerSections_additive : (coefficientTowerSections l E W).Additive := by
  unfold coefficientTowerSections
  infer_instance

/-- Additivity needed for the total right derived tower-sections functor.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientTowerSectionsAdditive :
    (coefficientTowerSections l E W).Additive := coefficientTowerSections_additive l E W

/-- The standard derived category of strict abelian-group towers.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientAbTowersDerived :
    HasDerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) := HasDerivedCategory.standard _

/-- The standard derived category of the mapping complexes' abelian groups.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientAbDerived :
    HasDerivedCategory AddCommGrpCat.{r} := HasDerivedCategory.standard _

/-- Abelian-group towers admit simultaneous K-injective resolutions.
Source: Stacks 079P, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: identify strict towers with abelian sheaves on the sequence site over a point.
This is Grothendieck abelian, so apply the functorial K-injective resolution theorem. -/
theorem coefficientAbTowers_haveKInjectives :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) := by
  sorry

/-- Simultaneous K-injectives for the mapping-complex towers.
Source: Stacks 079P, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientAbTowersKInjectives :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) :=
  coefficientAbTowers_haveKInjectives.{r}

/-- Inverse limit of abelian-group towers preserves addition.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: compose with every limit projection; the two maps become the same sum.
The projections jointly detect equality. -/
theorem coefficientAbLimit_additive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}).Additive := by
  exact Functor.additive_of_preserves_binary_products _

/-- Additivity for the mapping-complex total-limit functor.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientAbLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}).Additive :=
  coefficientAbLimit_additive.{r}

/-- The actual total right derived limit on mapping-complex towers.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable abbrev coefficientMappingLimit :
    DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      DerivedCategory AddCommGrpCat.{r} :=
  (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
    AddCommGrpCat.{r}).rightDerivedFunctor

/-- The derived evaluation on strict mapping-complex towers.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable abbrev coefficientMappingEvaluation (n : ℕ) :
    DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      DerivedCategory AddCommGrpCat.{r} :=
  ((evaluation ℕᵒᵖ AddCommGrpCat.{r}).obj (op n)).mapDerivedCategory

/-- Actual mapping-limit projections, fixed on simultaneous K-injective resolutions.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: apply the ordinary limit projection to a K-injective tower, use the exact
localization comparison for evaluation, and descend by the derived universal property.
Every tower has a K-injective representative; hence this characterization is unique. -/
theorem coefficientMappingProjection_exists (n : ℕ) :
    ∃! π : coefficientMappingLimit.{r} ⟶ coefficientMappingEvaluation.{r} n,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ℤ) [I.IsKInjective],
        π.app (DerivedCategory.Q.obj I) ≫
          ((evaluation ℕᵒᵖ AddCommGrpCat.{r}).obj
            (op n)).mapDerivedCategoryFactors.hom.app I =
        (Functor.rightDerivedFunctorObjQIso
          (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}) I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (lim.π (op n)) (ComplexShape.up ℤ)).app I) := by
  sorry

/-- The mapping-limit projection defined by its unique K-injective normalization.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientMappingProjection (n : ℕ) :=
  (coefficientMappingProjection_exists.{r} n).choose

/-- The coherent global derived mapping-complex system H_W.
It derives termwise global sections after exact scalar restriction of the actual
sequence-site internal Hom, and hence retains all strict transition data.
Source: Stacks 08JA, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientSequenceGlobalHom :
    (coefficientSequenceDerived l E W)ᵒᵖ × coefficientSequenceDerived l E W ⥤
      DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) :=
  coefficientSequenceInternalHom l E W ⋙ coefficientSequenceDerivedRestriction l E W ⋙
    (coefficientTowerSections l E W).rightDerivedFunctor
/-- The base-change map is defined by evaluation and tensor-Hom transposition.
This definition takes place in the derived categories, before any finite evaluation.
Source: Stacks 08J9 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def coefficientBaseChangeHom
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    F.obj (HA.obj (op P, Q)) ⟶ HB.obj (op (F.obj P), F.obj Q) :=
  SB.transpose _ (F.obj P) (F.obj Q)
    (μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q))

/-- Coherence of an evaluation-defined comparison, as actual system-map equations.
The transpose equation includes evaluation; the composition equation concerns internal
composition objects, and is stronger than preservation of composition on Hom sets.
Source: Stacks 08J9, 0A98 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientEvaluationCompatible
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop where
  /-- Naturality in both derived inputs. -/
  naturality : ∀ (P Q P' Q' : A) (f : P' ⟶ P) (g : Q ⟶ Q'),
    F.map (HA.map
        (Prod.mkHom (f.op) (g))) ≫ coefficientBaseChangeHom SA SB F μ P' Q' =
      coefficientBaseChangeHom SA SB F μ P Q ≫ HB.map
        (Prod.mkHom ((F.map f).op) (F.map g))
  /-- Compatibility with every tensor-Hom transpose, before evaluation at a level. -/
  transpose : ∀ (T P Q : A) (f : SA.tensor.obj (T, P) ⟶ Q),
    F.map (SA.transpose T P Q f) ≫ coefficientBaseChangeHom SA SB F μ P Q =
      SB.transpose (F.obj T) (F.obj P) (F.obj Q) (μ.inv.app (T, P) ≫ F.map f)
  /-- Compatibility with internal composition as a system morphism. -/
  composition : ∀ P Q V : A,
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map
        (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
          (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V)

/-- The enriched adjunction map, defined as the adjunct of base change followed
by internal Hom of the counit. Its invertibility is a conclusion of the calculus.
Source: Stacks 08J9, 07A6 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def coefficientEnrichedAdjunctionMap
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P : A) (N : B) :
    HA.obj (op P, G.obj N) ⟶ G.obj (HB.obj (op (F.obj P), N)) :=
  adj.homEquiv _ _
    (coefficientBaseChangeHom SA SB F μ P (G.obj N) ≫
      HB.map
        (Prod.mkHom (𝟙 _) (adj.counit.app N)))

/-- Successive actual coefficient restrictions equal restriction by the limit projection.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: the limit-cone equation identifies A→B_m→B_n with A→B_n. Restriction
composition is the identity on every section and every module morphism. -/
theorem coefficientRestrictionComp {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E W h ⋙ scalarReductionRestriction l E W m =
      scalarReductionRestriction l E W n := by
  sorry

/-- The ordinary tensor quotient map, as the scalar-extension adjunct of x↦x⊗1.
Source: Stacks 06YY, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientOrdinaryQuotientComponent {m n : ℕ} (h : n ≤ m)
    (M : scalarReductionSource l E W) :
    (scalarReductionExtension l E W m).obj M ⟶
      (normalizedDVRModuleRes l E W h).obj ((scalarReductionExtension l E W n).obj M) :=
  ((scalarReductionExtension_adjunction l E W m).choose.homEquiv _ _).symm
    ((scalarReductionExtension_adjunction l E W n).choose.unit.app M ≫
      (eqToIso (coefficientRestrictionComp l E W h)).inv.app
        ((scalarReductionExtension l E W n).obj M))

/-- The ordinary quotient components give a unique natural transformation.
Source: Stacks 06YY, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: naturality follows from the tensor/restriction Hom equivalence and naturality
of its unit. Its sections send x⊗b to x⊗ρ(b). The component formula gives uniqueness. -/
theorem coefficientOrdinaryQuotient_exists {m n : ℕ} (h : n ≤ m) :
    ∃! τ : scalarReductionExtension l E W m ⟶
      scalarReductionExtension l E W n ⋙ normalizedDVRModuleRes l E W h,
      ∀ M, τ.app M = coefficientOrdinaryQuotientComponent l E W h M := by
  sorry

/-- Strict quotient maps between the actual ordinary tensor reductions.
Source: Stacks 06YY, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientOrdinaryQuotient {m n : ℕ} (h : n ≤ m) :=
  (coefficientOrdinaryQuotient_exists l E W h).choose

/-- The additive structure of the recorded ordinary finite scalar extension.
This explicit instance exposes its existing structure without unfolding the derived witness.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientFiniteExtensionAdditive (n : ℕ) :
    (scalarReductionExtension l E W n).Additive :=
  (scalarReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose

/-- Finite reduction's universal counit is invertible on every K-flat representative.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: the recorded derived-change-of-rings witness provides its universal left derived
pair and asserts invertibility of this exact counit on K-flat complexes. Apply that last
clause to Q and hQ, with the standard localization and actual completion projection. -/
theorem coefficientFiniteReductionCounit_isIso
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (n : ℕ) : IsIso ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q)) := by
  exact (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.2.2 Q hQ

/-- The canonical computation of finite derived reduction on a K-flat complex.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteReductionModel
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (n : ℕ) :
    (coefficientFiniteDerivedExtension l E W n).obj (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
  letI : IsIso ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q)) :=
    coefficientFiniteReductionCounit_isIso l E W Q hQ n
  (coefficientFiniteDerivedExtension l E W n).mapIso
      ((DerivedCategory.quotientCompQhIso _).app Q).symm ≪≫
    asIso ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- Simultaneous K-flat computation of reduction, with its actual strict quotient maps.
The equality at each level also fixes how the model comparison meets the derived
finite-reduction comparison, so an unrelated isomorphism of evaluated objects cannot serve.
Source: Stacks 06YS, 06YY, 0941
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientReductionModels
    (R : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (ρ : ∀ n : ℕ, R ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q.X i)) →
    ∃ (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (e : R.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            Q),
      (∀ n : ℕ,
        (coefficientSequenceDerivedEvaluation l E W n).map e.hom ≫
          (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map (κ n).hom =
        (ρ n).hom.app (DerivedCategory.Q.obj Q) ≫
          (coefficientFiniteReductionModel l E W Q hQ n).hom) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
            (ComplexShape.up ℤ)).app C ≫
          ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (κ n).hom =
        (κ m).hom ≫ (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h)
          (ComplexShape.up ℤ)).app Q)
/-- The pure-tensor formula for a scalar tensor comparison, over general ring sheaves.
The same chain isomorphism must send every scalar-unit tensor generator to the tensor
of the scalar-unit sections. Specializing this predicate does not choose another map.
Source: Stacks 03EK, 07A4 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientScalarTensorGenerators
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A B : Sheaf J CommRingCat.{max c v u})
    (F : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) ⥤
      SheafOfModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj B))
    [hF : F.Additive]
    (η : ∀ (M : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) (V : Cᵒᵖ),
      M.val.obj V → (F.obj M).val.obj V)
    (P Q : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, c, v} J B).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)) : Prop :=
  ∀ (p q k : ℤ) (hpq : p + q = k) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    (e.hom.f k).val.app V
      (η (((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)).X k) V
        (coefficientTensorGenerator.{u, c, v} J A P Q p q k hpq V x y)) =
      coefficientTensorGenerator.{u, c, v} J B
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q k hpq V
        (η (P.X p) V x) (η (Q.X q) V y)

/-- The recorded integral-to-finite adjunction unit on the underlying local section.
Scalar restriction changes the action only, so this is the very same unit element.
Source: Stacks 03CZ, 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientIntegralScalarUnitSection (n : ℕ)
    (M : scalarReductionSource l E W) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((scalarReductionExtension l E W n).obj M).val.obj V :=
  (((scalarReductionExtension_adjunction l E W n).choose.unit.app M).val.app V x)

/-- The ordinary finite scalar-extension tensor comparison is uniquely fixed by
its unit formula on tensor generators, in every total-degree summand.
Source: Stacks 03EK, 07A4 (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: extension is sheafification of sectionwise scalar tensor. Send
b tensor (x tensor y) to (b tensor x) tensor (1 tensor y). Balancing gives the
inverse (b tensor x) tensor (c tensor y) ↦ bc tensor (x tensor y).
Both commute with restrictions and the signed total differential. Extension
preserves coproducts by its normalized adjunction. Sheafification and the tensor
universal properties make the generator equation determine every component. -/
theorem coefficientScalarTensorIso_exists (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ∃! e : ((scalarReductionExtension l E W n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      CoefficientScalarTensorGenerators.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        (integralCoefficientCommRingSheaf l E W n) (scalarReductionExtension l E W n)
        (hF := coefficientFiniteExtensionAdditive l E W n)
        (coefficientIntegralScalarUnitSection l E W n) P Q e := by
  sorry

/-- The unique ordinary scalar tensor comparison, with its generator normalization retained.
Source: Stacks 03EK, 07A4 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientScalarTensorIso (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :=
  (coefficientScalarTensorIso_exists l E W n P Q).choose

/-- Evaluation on sections, including the canonical coefficient-ring transport.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientEvaluationSection
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    ((coefficientSequenceEvaluation l E W n).obj M).val.obj U :=
  (eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U).symm) x

/-- Ordinary tensor evaluation is uniquely fixed on the actual sectionwise tensor generators.
Source: Stacks 03EK, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: restrict the tensor presheaf to the vertical slice and send x tensor y to
x tensor y. Vertical sheafification is the original site's sheafification, so this
gives an isomorphism of sheaf tensors. Evaluation preserves coproducts and is exact;
the comparisons assemble over total-degree summands, with the same signs in both
differentials. Generators before sheafification determine every component uniquely. -/
theorem coefficientEvaluationTensorIso_exists (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    ∃! e : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((coefficientTotalTensor.{u, t+1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      ∀ (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
        (x : (P.X p).val.obj (op (n, U.unop)))
        (y : (Q.X q).val.obj (op (n, U.unop))),
      (e.hom.f k).val.app U
        (coefficientEvaluationSection l E W _ n U
          (coefficientTensorGenerator.{u, t+1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) P Q p q k h
            (op (n, U.unop)) x y)) =
        coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q k h U
          (coefficientEvaluationSection l E W (P.X p) n U x)
          (coefficientEvaluationSection l E W (Q.X q) n U y) := by
  sorry

/-- The unique ordinary evaluation tensor comparison, fixed before deriving.
Source: Stacks 03EK, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientEvaluationTensorIso (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  (coefficientEvaluationTensorIso_exists l E W n P Q).choose

/-- Evaluation and finite scalar extension preserve the K-flat models in use.
Source: Stacks 06YN, 07A4, 0941
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: scalar extension carries a flat-term K-flat complex to a flat-term K-flat
complex by the tensor/restriction adjunction and associativity. For evaluation,
test acyclicity using induction from a level on the ringed sequence site; the
finite-prefix induction formula and exactness of evaluation give the K-flat test.
The same sheafified tensor computation preserves flatness term by term. -/
theorem coefficientTensorModelPreservation :
    (∀ (P : CochainComplex (scalarReductionSource l E W) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P →
      ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ∧
    (∀ (P : CochainComplex (coefficientSequenceModules l E W) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) P →
      ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) := by
  sorry



/-- Full data and identities of the coherent coefficient evaluation calculus.
The fields spell out each conclusion of the node. The normalized-system hypotheses
occur only where the node uses them; reduction and beta allow arbitrary ambient inputs.
Source: Stacks 06YS, 0A95, 0941, 079P and the agent-formulated enriched adjunction
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemTensors where
  /-- Closed derived tensor-Hom on completed coefficients. -/
  integralClosed : CoefficientClosedStructure (coefficientIntegralInternalHom l E W)
  /-- The tensor here is the ordinary K-flat derived tensor. -/
  integralTensorModel : CoefficientTensorModels.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) integralClosed
  /-- Closed derived tensor-Hom on the actual strict system category. -/
  systemClosed : CoefficientClosedStructure (coefficientSequenceInternalHom l E W)
  /-- The system tensor is derived before taking finite evaluations. -/
  systemTensorModel : CoefficientTensorModels.{u, t+1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) systemClosed
  /-- Closed derived tensor-Hom at every positive finite level. -/
  finiteClosed : ∀ n : ℕ, CoefficientClosedStructure (coefficientFiniteInternalHom l E W n)
  /-- Each finite tensor is the recorded total tensor on K-flat representatives. -/
  finiteTensorModel : ∀ n : ℕ, CoefficientTensorModels.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n) (finiteClosed n)
/-- The commutative quotient underlying the recorded scalar restriction.
Source: Stacks 06YY, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotient {m n : ℕ} (h : n ≤ m) :
    integralCoefficientCommRingSheaf l E W m ⟶ integralCoefficientCommRingSheaf l E W n where
  hom :=
    { app := fun V ↦ CommRingCat.ofHom ((normalizedDVRQuotient l E W h).hom.app V).hom
      naturality := fun {_ _} f ↦ (forget₂ CommRingCat RingCat).map_injective
        ((normalizedDVRQuotient l E W h).hom.naturality f) }

set_option linter.defProp false in
/-- The recorded universal change-of-rings witness, now for B_m → B_n.
Source: Stacks 06YY, node proof steps 5, 7 and 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientExistence {m n : ℕ} (h : n ≤ m) :=
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := Scheme.ProEt.topology W) (coefficientFiniteQuotient l E W h)

/-- Ordinary extension along the actual finite quotient, with tensor objects and maps fixed.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientExtension {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModules l E W m ⥤ normalizedDVRModules l E W n :=
  (coefficientFiniteQuotientExistence l E W h).choose

/-- The ordinary quotient extension has exactly the recorded sheafified tensor object.
Source: Stacks 06YY, node proof steps 5 and 10
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: specialize the object equality of the recorded derived-change-of-rings
witness used to define coefficientFiniteQuotientExtension. Its first component
is this very extension functor and its second component is the displayed equality. -/
theorem coefficientFiniteQuotientExtension_obj {m n : ℕ} (h : n ≤ m)
    (M : normalizedDVRModules l E W m) :
    (coefficientFiniteQuotientExtension l E W h).obj M =
      SheafOfModules.changeOfRings (coefficientFiniteQuotient l E W h) M := by
  sorry

/-- Additivity supplied by the recorded change-of-rings witness.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientFiniteQuotientExtensionAdditive {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientExtension l E W h).Additive :=
  (coefficientFiniteQuotientExistence l E W h).choose_spec.choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- The universal derived pair for the actual finite quotient.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientDerivedExistence {m n : ℕ} (h : n ≤ m) :=
  (coefficientFiniteQuotientExistence l E W h).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived scalar extension B_m → B_n from the recorded change-of-rings construction.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientDerived {m n : ℕ} (h : n ≤ m) :
    normalizedDVRDerived l E W m ⥤ normalizedDVRDerived l E W n :=
  (coefficientFiniteQuotientDerivedExistence l E W h).choose

/-- Its universal comparison on homotopy complexes, invertible on K-flat representatives.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientCounit {m n : ℕ} (h : n ≤ m) :
    DerivedCategory.Qh ⋙ coefficientFiniteQuotientDerived l E W h ⟶
      (coefficientFiniteQuotientExtension l E W h).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  (coefficientFiniteQuotientDerivedExistence l E W h).choose_spec.choose

/-- The recorded finite-quotient universal counit is invertible on K-flat complexes.
Source: Stacks 06YY, node proof steps 5, 7 and 10
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: specialize the K-flat counit clause of the recorded derived-change-of-rings
witness to the actual quotient B_m → B_n and the given representative. This is
exactly the universal counit used here, so no additional comparison is needed. -/
theorem coefficientFiniteQuotientCounit_isIso {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P) :
    IsIso ((coefficientFiniteQuotientCounit l E W h).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  sorry

/-- The canonical K-flat computation, using precisely the universal change-of-rings counit.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientModel {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P) :
    (coefficientFiniteQuotientDerived l E W h).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  letI := coefficientFiniteQuotientCounit_isIso l E W h P hP
  (coefficientFiniteQuotientDerived l E W h).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso ((coefficientFiniteQuotientCounit l E W h).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- Finite-quotient adjunction and tensor data, with both normalizations on representatives.
The ordinary unit is the actual sheafified 1 tensor x. The derived unit uses the
universal counit, and the tensor comparison preserves the same local pure tensors.
Source: Stacks 03CZ, 06YY, 07A4, 07A6, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientFiniteQuotientData (S : CoefficientDerivedSystemTensors l E W) where
  /-- Ordinary quotient extension is adjoint to the recorded exact scalar restriction. -/
  ordinaryAdjunction : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientFiniteQuotientExtension l E W h ⊣ normalizedDVRModuleRes l E W h
  /-- The derived quotient adjunction uses that same scalar restriction. -/
  adjunction : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientFiniteQuotientDerived l E W h ⊣ normalizedDVRRes l E W h
  /-- Quotient extension preserves K-flat representatives, without quotient-flatness. -/
  preservesKFlat : ∀ {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
      (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)
  /-- Strong tensor comparison used to reduce finite evaluation before transposing. -/
  tensor : ∀ {m n : ℕ} (h : n ≤ m),
    (S.finiteClosed m).tensor ⋙ coefficientFiniteQuotientDerived l E W h ≅
      (coefficientFiniteQuotientDerived l E W h).prod
        (coefficientFiniteQuotientDerived l E W h) ⋙ (S.finiteClosed n).tensor
/-- The ordinary scalar-unit section is sheafification of the module element 1 tensor x.
This general formula keeps coefficient constructions out of the sectionwise calculation.
Source: Stacks 03CZ, 03EK (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientChangeOfRingsUnitSection
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A B : Sheaf J CommRingCat.{max c v u}) (φ : A ⟶ B)
    (M : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (SheafOfModules.changeOfRings.{v, c, max c v u} φ M).val.obj V :=
  (toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v u} φ M).presheaf).app V
    ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app V).hom).unit.app (M.val.obj V) x)

/-- The actual finite-quotient tensor unit on a local section, with its scalar action displayed.
Source: Stacks 03CZ, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientUnitSection {m n : ℕ} (h : n ≤ m)
    (M : normalizedDVRModules l E W m) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((coefficientFiniteQuotientExtension l E W h).obj M).val.obj V :=
  (eqToHom (coefficientFiniteQuotientExtension_obj l E W h M).symm).val.app V
    (coefficientChangeOfRingsUnitSection.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W m) (integralCoefficientCommRingSheaf l E W n)
      (coefficientFiniteQuotient l E W h) M V x)

/-- Forget scalar restriction on a section, keeping its underlying element unchanged.
Source: Stacks 03CZ, 03DA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def coefficientRestrictionSection
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {A B : Sheaf J RingCat.{r}} (φ : A ⟶ B) (M : SheafOfModules.{r} B) (V : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars φ).obj M).val.obj V) : M.val.obj V := x

/-- The ordinary finite-quotient unit is actual sheafification of 1 tensor x.
Source: Stacks 03CZ, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteQuotientOrdinaryUnit (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientData l E W S) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m) (M : normalizedDVRModules l E W m)
    (V : W.ProEtᵒᵖ) (x : M.val.obj V),
    coefficientRestrictionSection (normalizedDVRQuotient l E W h)
      ((coefficientFiniteQuotientExtension l E W h).obj M) V
      (((D.ordinaryAdjunction h).unit.app M).val.app V x) =
        coefficientFiniteQuotientUnitSection l E W h M V x

/-- The derived finite-quotient unit is the localized ordinary unit through its counit.
Source: Stacks 06YY, 07A6, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteQuotientDerivedUnit (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientData l E W S) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P),
    (D.adjunction h).unit.app (DerivedCategory.Q.obj P) ≫
      (normalizedDVRRes l E W h).map (coefficientFiniteQuotientModel l E W h P hP).hom ≫
      (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.hom.app
        (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) =
    DerivedCategory.Q.map (((D.ordinaryAdjunction h).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app P)

/-- The exact K-flat quotient tensor normalization, packaged once as a proposition.
Source: Stacks 06YY, 07A4, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteQuotientTensorNormalization (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientData l E W S) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
    (P Q : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) Q),
    ∃ e : ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W m)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      CoefficientScalarTensorGenerators.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W m) (integralCoefficientCommRingSheaf l E W n)
        (coefficientFiniteQuotientExtension l E W h)
        (hF := coefficientFiniteQuotientExtensionAdditive l E W h)
        (coefficientFiniteQuotientUnitSection l E W h) P Q e ∧
      (coefficientFiniteQuotientDerived l E W h).map
          (((S.finiteTensorModel m).iso (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W m) (S.finiteClosed m) P Q hP hQ).hom) ≫
        (D.tensor h).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (S.finiteClosed n).tensor.map
          (Prod.mkHom (coefficientFiniteQuotientModel l E W h P hP).hom
            (coefficientFiniteQuotientModel l E W h Q hQ).hom) =
      (coefficientFiniteQuotientModel l E W h _
        (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W m) P Q hP hQ)).hom ≫
        DerivedCategory.Q.map e.hom ≫
        ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n) _ _
          (D.preservesKFlat h P hP) (D.preservesKFlat h Q hQ)).hom

/-- Finite-quotient data together with its actual pure-tensor K-flat normalization.
Source: Stacks 06YY, 07A4, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientFiniteQuotientCalculus (S : CoefficientDerivedSystemTensors l E W)
    extends CoefficientFiniteQuotientData l E W S where
  /-- The ordinary unit is the actual image of 1 tensor x under sheafification. -/
  ordinary_unit : CoefficientFiniteQuotientOrdinaryUnit l E W S toCoefficientFiniteQuotientData
  /-- The derived unit is the localized ordinary unit under the universal counit. -/
  unit_model : CoefficientFiniteQuotientDerivedUnit l E W S toCoefficientFiniteQuotientData
  /-- On K-flat representatives this is the ordinary pure-tensor chain isomorphism. -/
  tensor_model : CoefficientFiniteQuotientTensorNormalization l E W S
    toCoefficientFiniteQuotientData

/-- The actual transition-adjoint under the normalized finite-quotient adjunction.
Source: Stacks 07A6, 0941, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientSequenceTransitionAdjoint (_S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W _S) {m n : ℕ} (h : n ≤ m)
    (N : coefficientSequenceDerived l E W) :
    (coefficientFiniteQuotientDerived l E W h).obj
        ((coefficientSequenceDerivedEvaluation l E W m).obj N) ⟶
      (coefficientSequenceDerivedEvaluation l E W n).obj N :=
  ((D.adjunction h).homEquiv _ _).symm ((coefficientSequenceDerivedTransition l E W h).app N)

/-- The normalization criterion makes precisely this transition-adjoint invertible.
Source: Stacks 07A6, 0941, node proof steps 5 and 10
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: under the finite-quotient adjunction, precomposition by this adjunct is the
map f ↦ tau ≫ Res(f). The recorded normalization makes that map bijective for every
target. Yoneda therefore makes the adjunct an isomorphism, including m = n. -/
theorem coefficientSequenceTransitionAdjoint_isIso (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    IsIso (coefficientSequenceTransitionAdjoint l E W S D h N) := by
  apply isIso_of_coyoneda_map_bijective
  intro P
  apply Function.Bijective.of_comp_left
    (f := (D.adjunction h).homEquiv _ P)
  · simpa only [Function.comp_def, coefficientSequenceTransitionAdjoint,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] using hN h P
  · exact ((D.adjunction h).homEquiv _ P).injective

/-- The normalization isomorphism alpha is the actual transition-adjoint.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientSequenceNormalizationIso (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    (coefficientFiniteQuotientDerived l E W h).obj
        ((coefficientSequenceDerivedEvaluation l E W m).obj N) ≅
      (coefficientSequenceDerivedEvaluation l E W n).obj N :=
  letI := coefficientSequenceTransitionAdjoint_isIso l E W S D h N hN
  asIso (coefficientSequenceTransitionAdjoint l E W S D h N)

/-- The comparison c_(m,n) is reduced finite evaluation followed by tensor-Hom transpose.
Its tensor comparison is pinned to ordinary pure tensors by D.tensor_model.
Source: Stacks 08J9, 06YY, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientHomComparison (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    (P Q : normalizedDVRDerived l E W m) :
    (coefficientFiniteQuotientDerived l E W h).obj
        ((coefficientFiniteInternalHom l E W m).obj (op P, Q)) ⟶
      (coefficientFiniteInternalHom l E W n).obj
        (op ((coefficientFiniteQuotientDerived l E W h).obj P),
          (coefficientFiniteQuotientDerived l E W h).obj Q) :=
  coefficientBaseChangeHom (S.finiteClosed m) (S.finiteClosed n)
    (coefficientFiniteQuotientDerived l E W h) (D.tensor h) P Q

/-- Reduction and its normalized adjunction on the actual derived coefficient categories.
Source: Stacks 06YY, 07A6, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemReductionModel extends CoefficientDerivedSystemTensors l E W where
  /-- The reduction is a functor on the ordinary unbounded derived category. -/
  reduction : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W
  /-- Adjunction to the specified total limit, including both triangle identities. -/
  adjunction : reduction ⊣ coefficientSequenceLimit l E W
  /-- Finite evaluation is actual derived scalar extension. -/
  reductionEvaluation : ∀ n : ℕ,
    reduction ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n
  /-- Computation on a single flat-term K-flat representative with strict quotient maps. -/
  reductionModel : CoefficientReductionModels l E W reduction reductionEvaluation
  /-- Every ambient complex reduces to a normalized system. -/
  reduction_normalized : ∀ P, IsNormalizedCoefficientSequence l E W (reduction.obj P)
/-- The actual unit/counit projections and monoidal comparisons of reduction.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemReduction
    extends CoefficientDerivedSystemReductionModel l E W where
  /-- The reconstruction unit projects to the actual derived reduction map. -/
  unit_projection : ∀ (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    adjunction.unit.app P ≫ (coefficientSequenceProjection l E W n).app (reduction.obj P) =
      (coefficientFiniteAdjunction l E W n).unit.app P ≫
        (coefficientFiniteDerivedRestriction l E W n).map ((reductionEvaluation n).inv.app P)
  /-- The evaluated counit is exactly the adjunct of the total-limit projection. -/
  counit_projection : ∀ (N : coefficientSequenceDerived l E W) (n : ℕ),
    (coefficientFiniteAdjunction l E W n).homEquiv _ _
      ((reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj N) ≫
        (coefficientSequenceDerivedEvaluation l E W n).map (adjunction.counit.app N)) =
      (coefficientSequenceProjection l E W n).app N
  /-- Tensor reduction comparison in the derived system category itself. -/
  reductionTensor : integralClosed.tensor ⋙ reduction ≅
    reduction.prod reduction ⋙ systemClosed.tensor
  /-- Tensor comparison for actual finite scalar extension. -/
  finiteTensor : ∀ n : ℕ,
    integralClosed.tensor ⋙ coefficientFiniteDerivedExtension l E W n ≅
      (coefficientFiniteDerivedExtension l E W n).prod
        (coefficientFiniteDerivedExtension l E W n) ⋙ (finiteClosed n).tensor
  /-- Exact coefficient evaluation commutes with the derived system tensor. -/
  evaluationTensor : ∀ n : ℕ,
    systemClosed.tensor ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      (coefficientSequenceDerivedEvaluation l E W n).prod
        (coefficientSequenceDerivedEvaluation l E W n) ⋙ (finiteClosed n).tensor
/-- Finite scalar tensor comparison is the localization of the uniquely normalized
ordinary comparison. The square includes all representative identifications.
Source: Stacks 07A4, 06YU (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteTensorNormalization (S : CoefficientDerivedSystemReduction l E W) : Prop :=
  ∀ (n : ℕ) (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (coefficientFiniteDerivedExtension l E W n).map
      ((S.integralTensorModel.iso (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed P Q hP hQ).hom) ≫
      (S.finiteTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (S.finiteClosed n).tensor.map
        (Prod.mkHom (coefficientFiniteReductionModel l E W P hP n).hom
          (coefficientFiniteReductionModel l E W Q hQ n).hom) =
    (coefficientFiniteReductionModel l E W _
      (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ) n).hom ≫
      DerivedCategory.Q.map (coefficientScalarTensorIso l E W n P Q).hom ≫
      ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n) _ _
        ((coefficientTensorModelPreservation l E W).1 P hP n)
        ((coefficientTensorModelPreservation l E W).1 Q hQ n)).hom

/-- Evaluation tensor comparison is induced on simultaneous K-flat representatives
by the uniquely characterized ordinary evaluation comparison.
Source: Stacks 07A4, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientEvaluationTensorNormalization (S : CoefficientDerivedSystemReduction l E W) :
    Prop :=
  ∀ (n : ℕ) (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) Q),
    (coefficientSequenceDerivedEvaluation l E W n).map
      ((S.systemTensorModel.iso (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) S.systemClosed P Q hP hQ).hom) ≫
      (S.evaluationTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (S.finiteClosed n).tensor.map
        (Prod.mkHom ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P)
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app Q)) =
    (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (coefficientEvaluationTensorIso l E W n P Q).hom ≫
      ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n) _ _
        ((coefficientTensorModelPreservation l E W).2 P hP n)
        ((coefficientTensorModelPreservation l E W).2 Q hQ n)).hom

/-- Reduction tensor comparison evaluates to the same normalized scalar-extension
comparison, with the actual reduction and tensor-evaluation identifications.
Source: Stacks 07A4, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientReductionTensorEvaluation (S : CoefficientDerivedSystemReduction l E W) : Prop :=
  ∀ (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        (S.reductionTensor.hom.app (P, Q)) ≫
      (S.evaluationTensor n).hom.app (S.reduction.obj P, S.reduction.obj Q) ≫
      (S.finiteClosed n).tensor.map
        (Prod.mkHom ((S.reductionEvaluation n).hom.app P)
          ((S.reductionEvaluation n).hom.app Q)) =
    (S.reductionEvaluation n).hom.app (S.integralClosed.tensor.obj (P, Q)) ≫
      (S.finiteTensor n).hom.app (P, Q)

/-- A single strict reduction presentation with all finite and horizontal identifications.
This is the presentation already required in CoefficientReductionModels, exposed so
that the tensor comparison can be specified on the very same presentations.
Source: Stacks 06YS, 06YY, 0941
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientReductionPresentation
    (S : CoefficientDerivedSystemReduction l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :
    Prop :=
  (∀ n : ℕ,
    (coefficientSequenceDerivedEvaluation l E W n).map e.hom ≫
      (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C ≫
      DerivedCategory.Q.map (κ n).hom =
    (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
      (coefficientFiniteReductionModel l E W P hP n).hom) ∧
  (∀ (m n : ℕ) (h : n ≤ m),
    (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
        (ComplexShape.up ℤ)).app C ≫
      ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (κ n).hom =
    (κ m).hom ≫ (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h)
      (ComplexShape.up ℤ)).app P)

/-- The reduction tensor map is induced by one strict chain map whose finite components
are the ordinary normalized scalar tensor maps. Its square is an equality in the
system derived category, before evaluation or taking a limit.
Source: Stacks 07A4, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientReductionTensorNormalization (S : CoefficientDerivedSystemReduction l E W) :
    Prop :=
  ∀ (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)) →
    ∃ (C D Z : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) C)
      (hD : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) D)
      (eC : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
      (eD : S.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj D)
      (eZ : S.reduction.obj (DerivedCategory.Q.obj
        ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q))) ≅
        DerivedCategory.Q.obj Z)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          D ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            Q)
      (κZ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          Z ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)))
      (ψ : Z ⟶ (coefficientTotalTensor.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (C, D)),
      CoefficientReductionPresentation l E W S P hP C eC κC ∧
      CoefficientReductionPresentation l E W S Q hQ D eD κD ∧
      CoefficientReductionPresentation l E W S _
        (coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ) Z eZ κZ ∧
      (∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ψ ≫ (coefficientEvaluationTensorIso l E W n C D).hom ≫
          (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W n)).map
              (Prod.mkHom (κC n).hom (κD n).hom) =
        (κZ n).hom ≫ (coefficientScalarTensorIso l E W n P Q).hom) ∧
      S.reduction.map ((S.integralTensorModel.iso (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) S.integralClosed P Q hP hQ).hom) ≫
        S.reductionTensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom) =
      eZ.hom ≫ DerivedCategory.Q.map ψ ≫
        (S.systemTensorModel.iso (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) S.systemClosed C D hC hD).hom

/-- The actual internal-Hom transition under its fiber identifications.
This is the transition-adjoint formula for normalized inputs, using the finite quotient
comparison obtained by transposing reduced evaluation with its K-flat tensor normalization.
Source: Stacks 06YY, 07A6, 0941, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiberTransition (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S)
    (fiberHom : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)) : Prop :=
  ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) {m n : ℕ} (h : n ≤ m),
    coefficientSequenceTransitionAdjoint l E W S
        D h ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≫
      (fiberHom M N hM hN n).hom =
    (coefficientFiniteQuotientDerived l E W h).map ((fiberHom M N hM hN m).hom) ≫
      coefficientFiniteQuotientHomComparison l E W S
        D h ((coefficientSequenceDerivedEvaluation l E W m).obj M)
          ((coefficientSequenceDerivedEvaluation l E W m).obj N) ≫
      (coefficientFiniteInternalHom l E W n).map
        (Prod.mkHom ((coefficientSequenceNormalizationIso l E W
          S D h M hM).inv.op)
          (coefficientSequenceNormalizationIso l E W
            S D h N hN).hom)

/-- Coherent fibers and evaluation on the canonical reduction data.
Source: Stacks 0A95, 0941 and node proof steps 6--11
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemFibers extends CoefficientDerivedSystemReduction l E W where
  /-- Reduction's tensor comparison has the simultaneous strict representative formula. -/
  reductionTensor_normalization : CoefficientReductionTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Finite tensor comparisons have their ordinary generator normalization. -/
  finiteTensor_normalization : CoefficientFiniteTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Evaluation tensor comparisons have their simultaneous representative normalization. -/
  evaluationTensor_normalization : CoefficientEvaluationTensorNormalization l E W
    toCoefficientDerivedSystemReduction
  /-- Reduction uses precisely the normalized finite tensor comparisons at each level. -/
  reductionTensor_evaluation : CoefficientReductionTensorEvaluation l E W
    toCoefficientDerivedSystemReduction

  /-- Actual quotient scalar extension with its adjunction and K-flat tensor normalization. -/
  quotientCalculus : CoefficientFiniteQuotientCalculus l E W toCoefficientDerivedSystemTensors

  /-- Beta preserves evaluation, transposes and internal composition as system maps. -/
  reduction_compatible : CoefficientEvaluationCompatible integralClosed systemClosed
    reduction reductionTensor
  /-- Finite comparisons use the same evaluation-defined tensor-Hom calculus. -/
  finite_compatible : ∀ n : ℕ, CoefficientEvaluationCompatible integralClosed (finiteClosed n)
    (coefficientFiniteDerivedExtension l E W n) (finiteTensor n)
  /-- Internal Hom on normalized inputs has exactly the finite internal-Hom fibers. -/
  fiberHom : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- The fiber identification is induced by simultaneous system evaluation. -/
  fiber_evaluation : ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ),
    (evaluationTensor n).inv.app
        ((coefficientSequenceInternalHom l E W).obj (op M, N), M) ≫
      (coefficientSequenceDerivedEvaluation l E W n).map (systemClosed.evaluation M N) =
    (finiteClosed n).tensor.map
        (Prod.mkHom ((fiberHom M N hM hN n).hom) (𝟙 _)) ≫
      (finiteClosed n).evaluation
        ((coefficientSequenceDerivedEvaluation l E W n).obj M)
        ((coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- Fiberwise internal Hom is natural for input derived morphisms. -/
  fiber_naturality : ∀ (M N M' N' : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N)
    (hM' : IsNormalizedCoefficientSequence l E W M')
    (hN' : IsNormalizedCoefficientSequence l E W N') (f : M' ⟶ M) (g : N ⟶ N') (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        ((coefficientSequenceInternalHom l E W).map
        (Prod.mkHom (f.op) (g))) ≫
      (fiberHom M' N' hM' hN' n).hom =
    (fiberHom M N hM hN n).hom ≫ (coefficientFiniteInternalHom l E W n).map
      (Prod.mkHom (((coefficientSequenceDerivedEvaluation l E W n).map f).op)
        ((coefficientSequenceDerivedEvaluation l E W n).map g))
  /-- The adjunct of the actual `coefficientSequenceDerivedTransition` on internal Hom,
  under `fiberHom` at m and n, is c_(m,n) followed by RHom(alpha_M inverse, alpha_N).
  Here c_(m,n) transposes reduced finite evaluation using `quotientCalculus.tensor`,
  whose `tensor_model` fixes its comparison on every pair of K-flat representatives. -/
  fiber_transition : CoefficientFiberTransition l E W toCoefficientDerivedSystemTensors
    quotientCalculus fiberHom
  /-- Beta evaluates to the usual finite internal-Hom reduction comparison. -/
  beta_evaluation : ∀ (P Q : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        (coefficientBaseChangeHom integralClosed systemClosed reduction reductionTensor P Q) ≫
      (fiberHom _ _ (reduction_normalized P) (reduction_normalized Q) n).hom =
    (reductionEvaluation n).hom.app ((coefficientIntegralInternalHom l E W).obj (op P, Q)) ≫
      coefficientBaseChangeHom integralClosed (finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n) (finiteTensor n) P Q ≫
      (coefficientFiniteInternalHom l E W n).map
        (Prod.mkHom (((reductionEvaluation n).hom.app P).op) ((reductionEvaluation n).inv.app Q))
  /-- Joint conservativity on actual derived system maps. -/
  isIso_iff_evaluations : ∀ {M N : coefficientSequenceDerived l E W} (f : M ⟶ N),
    IsIso f ↔ ∀ n : ℕ, IsIso ((coefficientSequenceDerivedEvaluation l E W n).map f)
  /-- Total derived global sections of a system retain its finite fibers. -/
  globalEvaluation : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientMappingEvaluation.{max u (t+1)} n).obj
          ((coefficientSequenceGlobalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteGlobalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
/-- The full calculus additionally carries its enriched and global-limit comparisons.
Source: Stacks 08J9, 07A6, 0941 and node proof steps 12--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemCalculus extends CoefficientDerivedSystemFibers l E W where
  /-- Enriched adjunction is invertible, without asserting completeness of P or N. -/
  enriched_isIso : ∀ (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W), IsNormalizedCoefficientSequence l E W N →
    IsIso (coefficientEnrichedAdjunctionMap integralClosed systemClosed reduction adjunction
      reductionTensor P N)
  /-- Global sections commute with the specified total limit, naturally as derived functors. -/
  globalLimit : coefficientSequenceLimit l E W ⋙
      coefficientIntegralSections l E W ≅
    coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
        coefficientMappingLimit.{max u (t+1)}
/-- The global comparison gamma is the global sections of the specified enriched adjunct,
followed by the specified total-limit comparison. Thus its data are real composites.
Source: Stacks 08J9, 07A6, 0941 and node proof steps 12--14
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def CoefficientDerivedSystemCalculus.gamma
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    (coefficientIntegralGlobalHom l E W).obj
        (op P, (coefficientSequenceLimit l E W).obj N) ≅
      coefficientMappingLimit.{max u (t+1)}.obj
        ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N)) :=
  letI := S.enriched_isIso P N hN
  (coefficientIntegralSections l E W).mapIso
      (asIso (coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
        S.adjunction S.reductionTensor P N)) ≪≫
    S.globalLimit.app
      ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))

/-- The lax tensor comparison of the right adjoint, defined by the counit mate.
Source: Stacks 07A6 and node proof step 15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def CoefficientDerivedSystemCalculus.tensorLimitMap
    (S : CoefficientDerivedSystemCalculus l E W)
    (T : DerivedCategory (scalarReductionSource l E W)) (N : coefficientSequenceDerived l E W) :
    S.integralClosed.tensor.obj (T, (coefficientSequenceLimit l E W).obj N) ⟶
      (coefficientSequenceLimit l E W).obj
        (S.systemClosed.tensor.obj (S.reduction.obj T, N)) :=
  S.adjunction.homEquiv _ _
    ((S.reductionTensor).hom.app (T, (coefficientSequenceLimit l E W).obj N) ≫
      S.systemClosed.tensor.map
        (Prod.mkHom (𝟙 (S.reduction.obj T)) (S.adjunction.counit.app N)))



/-- Ordinary global sections commute with inverse limit by the actual projections.
Source: Stacks 0941 and node proof step 12
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: Hom from the module unit preserves limits. The ordinary comparison sends a
section of the limit to its compatible family of sections. The inverse uses the limit
universal property. These maps commute with all projections and determine each other
uniquely; the same characterization proves naturality in the tower. -/
theorem coefficientSectionsLimitIso_exists :
    ∃! e : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) ⋙
        coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) ≅
      coefficientTowerSections l E W ⋙
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) ⥤ AddCommGrpCat.{max u (t+1)}),
      ∀ (T : ℕᵒᵖ ⥤ scalarReductionSource l E W) (n : ℕ),
        e.hom.app T ≫ (lim.π (op n)).app ((coefficientTowerSections l E W).obj T) =
          (coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).map ((lim.π (op n)).app T) := by
  sorry

/-- The unique ordinary sections/limit comparison used by the derived normalization.
Source: Stacks 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientSectionsLimitIso :=
  (coefficientSectionsLimitIso_exists l E W).choose

/-- The left composite universal comparison, from ordinary sections of the ordinary limit.
Source: Stacks 079P, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientGlobalLimitLeftComparison
    (K : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :=
  coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      ((Functor.mapHomologicalComplex
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
        (ComplexShape.up ℤ)).obj K) ≫
    (coefficientIntegralSections l E W).map
        (coefficientRightDerivedComparison
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) K)

/-- The right composite universal comparison, after ordinary sections/limit commutation.
Source: Stacks 079P, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientGlobalLimitRightComparison
    (K : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :=
  DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (coefficientSectionsLimitIso l E W).hom
        (ComplexShape.up ℤ)).app K) ≫
    coefficientRightDerivedComparison
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) ⥤ AddCommGrpCat.{max u (t+1)})
      (((coefficientTowerSections l E W).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
    coefficientMappingLimit.{max u (t+1)}.map
      (coefficientRightDerivedComparison (coefficientTowerSections l E W) K)

/-- Scalar restriction preserves finite limits with the exact recorded functor.
Source: Stacks 03DA, 03CZ (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientFiniteRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (scalarReductionRestriction l E W n) :=
  (scalarReductionRestriction_exact l E W n).1

/-- Scalar restriction preserves finite colimits with the exact recorded functor.
Source: Stacks 03DA, 03CZ (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientFiniteRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (scalarReductionRestriction l E W n) :=
  (scalarReductionRestriction_exact l E W n).2

/-- Projection, resolution, naturality and composition normalizations for the calculus.
These equations specify gamma and its actual total-limit projections simultaneously.
Source: node proof steps 12--15, Stacks 08J9, 07A6, 0941
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemScalarData where
  /-- Global sections after scalar restriction have the canonical finite meaning. -/
  scalarSections : ∀ n : ℕ,
    coefficientFiniteDerivedRestriction l E W n ⋙
      coefficientIntegralSections l E W ≅
      coefficientFiniteSections l E W n
  /-- Ordinary scalar-section transport is fixed on actual section maps. -/
  ordinaryScalarSections : ∀ n : ℕ,
    scalarReductionRestriction l E W n ⋙
      coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ≅
    coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
/-- The ordinary section transport is characterized on all section maps.
Source: Stacks 03CZ, 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientOrdinaryScalarSectionsFormula
    (D : CoefficientDerivedSystemScalarData l E W) : Prop :=
  ∀ (n : ℕ) (M : scalarReductionTarget l E W n)
    (f : SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (scalarReductionRestriction l E W n).obj M)
    (V : W.ProEtᵒᵖ) (b : (integralCoefficientSheaf l E W n).obj.obj V),
    (((D.ordinaryScalarSections n).hom.app M) f).val.app V b = b • (@id (M.val.obj V) (f.val.app V
      (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj V)))

/-- Compatibility of scalar-section transport with the universal derived comparisons.
Source: Stacks 079P, 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientScalarSectionsModel
    (D : CoefficientDerivedSystemScalarData l E W) : Prop :=
  ∀ (n : ℕ) (I : CochainComplex (scalarReductionTarget l E W n) ℤ),
    coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        (((scalarReductionRestriction l E W n).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≫
      (coefficientIntegralSections l E W).map
          ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app I) ≫
      (D.scalarSections n).hom.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (D.ordinaryScalarSections n).hom
      (ComplexShape.up ℤ)).app I) ≫
      coefficientSiteSectionsComparison.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) I

/-- The canonical scalar-section comparisons and their resolution normalization.
Source: Stacks 03CZ, 079P, 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemScalarCoherence
    extends CoefficientDerivedSystemScalarData l E W where
  /-- The ordinary transport acts by the actual sectionwise adjunct. -/
  ordinaryScalarSections_formula : CoefficientOrdinaryScalarSectionsFormula l E W
    toCoefficientDerivedSystemScalarData
  /-- The derived comparison extends the ordinary transport on all complexes. -/
  scalarSections_model : CoefficientScalarSectionsModel l E W
    toCoefficientDerivedSystemScalarData

/-- The simultaneous-resolution equation for the actual global-limit comparison.
This is the original model equation, packaged once to avoid duplicating its large
localization terms in every generated structure declaration.
Source: Stacks 079P, 0941, node proof steps 12--14
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientGlobalLimitModel (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (K : CochainComplex (coefficientSequenceModules l E W) ℤ),
    coefficientGlobalLimitLeftComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      (coefficientIntegralSections l E W).map
          ((coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)) ≫
      S.globalLimit.hom.app (DerivedCategory.Q.obj K) =
    coefficientGlobalLimitRightComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      coefficientMappingLimit.{max u (t+1)}.map
        ((coefficientTowerSections l E W).rightDerivedFunctor.map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K))

/-- The resolution normalization of the global mapping-system comparisons.
Source: Stacks 079P, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemResolutionCoherence
    (S : CoefficientDerivedSystemCalculus l E W)
    extends CoefficientDerivedSystemScalarCoherence l E W where
  /-- Derived termwise sections commute with evaluation, before taking internal Hom. -/
  systemSectionsEvaluation : ∀ n : ℕ,
    coefficientSequenceDerivedRestriction l E W ⋙
        (coefficientTowerSections l E W).rightDerivedFunctor ⋙
          coefficientMappingEvaluation.{max u (t+1)} n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙
        coefficientFiniteSections l E W n
  /-- The finite global-Hom identification is obtained from the actual internal-Hom fiber. -/
  globalEvaluation_model : ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ),
    (S.globalEvaluation M N hM hN n).hom =
      (systemSectionsEvaluation n).hom.app
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≫
        (coefficientFiniteSections l E W n).map ((S.fiberHom M N hM hN n).hom)
  /-- The global-limit comparison is the simultaneous derived ordinary comparison. -/
  globalLimit_model : CoefficientGlobalLimitModel l E W S
/-- The finite enriched isIso equation of the coefficient calculus.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientFiniteEnrichedIsIso (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (n : ℕ) (P : DerivedCategory (scalarReductionSource l E W))
    (M : normalizedDVRDerived l E W n),
    IsIso (coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
      (coefficientFiniteDerivedExtension l E W n) (coefficientFiniteAdjunction l E W n)
          (S.finiteTensor n) P M)

/-- The gamma projection equation of the coefficient calculus.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientGammaProjection (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S) : Prop :=
  ∀ (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N)
    (n : ℕ),
    (S.gamma l E W P N hN).hom ≫
      (coefficientMappingProjection.{max u (t+1)} n).app
        ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N)) ≫
      (S.globalEvaluation _ _ (S.reduction_normalized P) hN n).hom =
    (coefficientIntegralGlobalHom l E W).map
        (Prod.mkHom (𝟙 (op P)) ((coefficientSequenceProjection l E W n).app N)) ≫
      (coefficientIntegralSections l E W).map
        (coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
          (coefficientFiniteDerivedExtension l E W n) (coefficientFiniteAdjunction l E W n)
          (S.finiteTensor n)
          P ((coefficientSequenceDerivedEvaluation l E W n).obj N)) ≫
      (D.scalarSections n).hom.app ((coefficientFiniteInternalHom l E W n).obj
        (op ((coefficientFiniteDerivedExtension l E W n).obj P),
          (coefficientSequenceDerivedEvaluation l E W n).obj N)) ≫
      (coefficientFiniteGlobalHom l E W n).map
        (Prod.mkHom (((S.reductionEvaluation n).hom.app P).op)
          (𝟙 ((coefficientSequenceDerivedEvaluation l E W n).obj N)))

/-- The gamma naturality equation of the coefficient calculus.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientGammaNaturality (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (P P' : DerivedCategory (scalarReductionSource l E W))
    (N N' : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N)
    (hN' : IsNormalizedCoefficientSequence l E W N') (a : P' ⟶ P) (b : N ⟶ N'),
    (coefficientIntegralGlobalHom l E W).map
        (Prod.mkHom (a.op) ((coefficientSequenceLimit l E W).map b)) ≫
      (S.gamma l E W P' N' hN').hom =
    (S.gamma l E W P N hN).hom ≫ coefficientMappingLimit.{max u (t+1)}.map
      ((coefficientSequenceGlobalHom l E W).map
        (Prod.mkHom ((S.reduction.map a).op) (b)))

/-- The recorded additive identification of integral H⁰ RHom with derived morphisms.
Source: Stacks 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientIntegralHomEquiv
    (P Q : DerivedCategory (scalarReductionSource l E W)) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj (op P, Q))) ≃+ (P ⟶ Q) :=
  (coefficientHomZeroEquiv.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)) P Q

/-- The recorded additive identification of finite H⁰ RHom with derived morphisms.
Source: Stacks 08JA (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteHomEquiv (n : ℕ)
    (P Q : normalizedDVRDerived l E W n) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
      ((coefficientFiniteGlobalHom l E W n).obj (op P, Q))) ≃+ (P ⟶ Q) :=
  (coefficientHomZeroEquiv.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)) P Q

/-- The actual H⁰ map of gamma itself, before taking any mapping-limit projection.
Source: Stacks 07A6, 08JA, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientGammaZero
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
        ((coefficientIntegralGlobalHom l E W).obj (op P,
          (coefficientSequenceLimit l E W).obj N)) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
        (coefficientMappingLimit.{max u (t+1)}.obj
          ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N))) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).map
    (S.gamma l E W P N hN).hom

/-- The actual H⁰ map of gamma followed by its nth mapping-limit projection and
finite global-Hom identification. This is the map used in the degree-zero formula,
so the formula cannot be satisfied by an unrelated additive equivalence.
Source: Stacks 07A6, 08JA, 0941 (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientGammaZeroMap
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
        ((coefficientIntegralGlobalHom l E W).obj (op P,
          (coefficientSequenceLimit l E W).obj N)) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).obj
        ((coefficientFiniteGlobalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj
            (S.reduction.obj P)),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)) :=
  coefficientGammaZero l E W S P N hN ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t+1)} 0).map
      ((coefficientMappingProjection.{max u (t+1)} n).app
          ((coefficientSequenceGlobalHom l E W).obj (op (S.reduction.obj P), N)) ≫
        (S.globalEvaluation _ _ (S.reduction_normalized P) hN n).hom)

/-- The actual degree-zero map of gamma, followed by its actual nth projection,
under the recorded H⁰ RHom identifications, sends h to reduction of h followed
by the evaluated counit. Normalization of N is precisely gamma's domain condition.
Source: Stacks 07A6, 08JA, 0941 and node proof step 14
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientHomProjection (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N)
    (h : P ⟶ (coefficientSequenceLimit l E W).obj N) (n : ℕ),
    coefficientFiniteHomEquiv l E W n _ _
      ((coefficientGammaZeroMap l E W S P N hN n)
        ((coefficientIntegralHomEquiv l E W P _).symm h)) =
      (S.reductionEvaluation n).hom.app P ≫
        (coefficientFiniteDerivedExtension l E W n).map h ≫
        (S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj N) ≫
        (coefficientSequenceDerivedEvaluation l E W n).map (S.adjunction.counit.app N)

/-- The composition equation of the coefficient calculus.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
def CoefficientMappingComposition (S : CoefficientDerivedSystemCalculus l E W) : Prop :=
  ∀ (T U P : DerivedCategory (scalarReductionSource l E W))
    (N N' : coefficientSequenceDerived l E W)
    (f : S.integralClosed.tensor.obj (T, P) ⟶ (coefficientSequenceLimit l E W).obj N)
    (g : S.systemClosed.tensor.obj (S.reduction.obj U, N) ⟶ N'),
    S.adjunction.homEquiv _ _
      ((S.reductionTensor).hom.app (U, S.integralClosed.tensor.obj (T, P)) ≫
        S.systemClosed.tensor.map
        (Prod.mkHom (𝟙 (S.reduction.obj U)) ((S.adjunction.homEquiv _ _).symm f)) ≫ g) =
    S.integralClosed.tensor.map
        (Prod.mkHom (𝟙 U) (f)) ≫ S.tensorLimitMap l E W U N ≫
      (coefficientSequenceLimit l E W).map g

/-- The specified finite projections, naturality and composition of gamma.
Source: Stacks 07A6, 0941 and node proof steps 14--15
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
structure CoefficientDerivedSystemCoherence (S : CoefficientDerivedSystemCalculus l E W)
    extends CoefficientDerivedSystemResolutionCoherence l E W S where
  /-- finite enriched isIso. -/
  finite_enriched_isIso : CoefficientFiniteEnrichedIsIso l E W S
  /-- gamma projection. -/
  gamma_projection : CoefficientGammaProjection l E W S
    toCoefficientDerivedSystemResolutionCoherence
  /-- gamma naturality. -/
  gamma_naturality : CoefficientGammaNaturality l E W S
  /-- hom projection. -/
  hom_projection : CoefficientHomProjection l E W S
  /-- composition. -/
  composition : CoefficientMappingComposition l E W S

/-- The full coherent derived reduction, limit adjunction and fiberwise evaluation calculus.
Source: Stacks 06YS, 0A95, 0941, 079P; the enriched varying-coefficient comparison
is the agent-formulated construction in the node
(blueprint: lem-coef-derived-system-evaluation-calculus).

Proof, following the node step by step:
1. Modules over the actual sequence ring are the strict semilinear systems. Apply
prop-pur-kinjective-resolutions-exist and lem-pc-kflat-resolution on that small site.
2. Derive the ordinary tensor/direct-image adjunction for the sequence projection by
lem-weil-pbc-ringed-topoi-derived-pullback and lem-pc-pre-derived-adjoint-functors-general.
3. Factor direct image through exact scalar restriction and the constant-ring sequence
projection. The composition comparison identifies its total right derived functor with L.
4. The normalized fraction formula identifies unit and counit with the actual reduction
maps and total-limit projections, using lem-weil-derived-scalar-extension-restriction-adjunction.
5. Evaluation is exact and jointly detects acyclicity, hence derived isomorphisms.
Compute tensor and reduction on one flat-term K-flat representative and its quotient maps.
Fix ordinary tensor comparisons by their formulas on pure tensors. The reduction tensor
square is induced by one strict chain map with these components; the finite and
evaluation tensor squares are its localized ordinary scalar-extension and slice maps.
6. Derive simultaneous Hom on the sequence site; 0A95 gives independence of representatives.
The tensor-Hom currying theorem and rhom-global-sections give closed evaluation/transposition.
Normalize currying itself by componentwise evaluation into the fixed K-injective
replacement. Under the total-tensor comparison it sends x tensor y to phi(x)(y).
7. Derive induction from a level by extending its finite prefix and setting the higher
levels to zero; finite quotient extension is computed by K-flat representatives.
8. The prefix computation and normalization give the induction projection formula.
9. Yoneda applied to that projection formula identifies the evaluated system Hom with the
finite Hom. The identification is fixed by evaluation, and is natural in both inputs.
10. For normalized inputs the horizontal restrictions of simultaneous Hom are exactly the
scalar-extension comparisons, by the evaluated tensor-Hom adjunction and its normalization.
11. Define beta by reducing evaluation and transposing. Uncurrying verifies the finite
formula, transposition compatibility and the internal composition equation as system maps.
12. Derive termwise global sections after U. Evaluation on constant-ring towers preserves
K-injectives; derive ordinary commutation of sections and limit, with its actual projections.
13. The adjunct of beta followed by internal Hom of the counit is the enriched map delta.
The natural tensor-Hom and reduction/limit Hom bijections, followed by Yoneda, make it an
isomorphism. Apply global sections and step 12 to obtain the specified gamma.
14. Uncurry its nth projection. It is evaluation followed by the counit at n, hence by
step 4 is exactly the scalar-extension adjunct of the total-limit projection. On Hom-zero
it sends h to the evaluated counit after derived reduction of h: apply H-zero to the
actual composite of gamma, the mapping-limit projection, and the global fiber comparison,
and use the recorded integral and finite H-zero RHom identifications.
15. Counit naturality gives naturality of delta and gamma. Uncurrying the two composites
with tensor parameters gives g after (1 tensor f-sharp) on both sides. This gives mapping
composition, evaluation, transposition and unit/counit compatibility; the Hom-complex
Leibniz differential supplies the usual signs. No reconstruction or invertibility of beta
or the reconstruction unit on arbitrary inputs is claimed. -/
theorem coefficientDerivedSystemEvaluationCalculus :
    ∃ S : CoefficientDerivedSystemCalculus l E W,
      Nonempty (CoefficientDerivedSystemCoherence l E W S) := by
  sorry

end WeilConjectures
