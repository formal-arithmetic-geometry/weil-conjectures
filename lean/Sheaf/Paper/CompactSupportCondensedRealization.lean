/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.CondensedCompactSupportProjection
public import Sheaf.Paper.SemilinearCompactSupportCoefficientTransport
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CondensedERealization
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Paper.CondensedCoefficientComparisons
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.BasicOperationsCoefficientReduction

import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.Paper.IntegralCompactSupportUniformRestriction
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence
import Sheaf.CategoryTheory.StrictTowerArithmeticRestriction
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation
import Sheaf.Paper.CondensedFlatCoefficientCalculus
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.CompletedDirectImageLimits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Sheaf.Paper.PbcRationalTransport

/-! # Compact-support condensed realization

Source: Bhatt--Scholze 6.7.2, 6.7.14--6.7.17, 6.8.14--6.8.15;
blueprint sk-thm-purity-transport, Steps 2--3.
(blueprint: lem-pur-compact-support-condensed-realization).

## Main definitions and statements

- `IntegralModel`, `alpha`: actual strict-tower reconstruction and its counit.
- `condensedProjection`: the original proper/open scalar projection.
- `FiniteComparison`: full-system and rationalized coefficient compatibility.
- `systemRefinement`, `fieldRefinement`: unit-normalized refinement arrows.
- `ComparisonFamily`, `compactSupport_condensedRealization`: simultaneous comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory


attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] WeilConjectures.integralCoefficientCommRingSheaf

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]


/-- The strict completed-coefficient tower is constructed by reduction, whole-system
proper/open operations, and the dependency's exact coefficient restriction.
Source: blueprint proof Step 3; Bhatt--Scholze 6.7.6
(blueprint: lem-pur-compact-support-condensed-realization). -/
def strictTower {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) :=
  R.reduction ⋙ systemSupport l E c ⋙ coefficientSequenceDerivedRestriction.{u, u} l E Y

/-- The actual total derived limit of that strict tower, transported through the
published completed-coefficient presentation. No vertex of a bare derived-category
cone is selected. Source: blueprint proof Step 3; Bhatt--Scholze 6.7.6
(blueprint: lem-pur-compact-support-condensed-realization). -/
def rawSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    PbcCompletedDerived X (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived Y (pbcIntegralDatum l E) :=
  (purCoefficientModel l E X).functor ⋙ strictTower l E c R ⋙
    coefficientConstantTowerLimit.{u, u} l E Y ⋙ (purCoefficientModel l E Y).inverse

/-- Integral reconstruction data. The underlying functor is literally the total-limit
composite just defined; the reduction isomorphism below will be its counit.
Source: blueprint proof Steps 1--3; Bhatt--Scholze 6.7.2 and 6.7.7
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure IntegralModel {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W) where
  preserves : ∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) K →
      PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
        ((rawSupport l E c (R X)).obj K)
  [additive : (rawSupport l E c (R X)).Additive]
  [linear : (rawSupport l E c (R X)).Linear (PbcIntegralRing l E)]
  [commShift : (rawSupport l E c (R X)).CommShift ℤ]
  triangulated :
    @Functor.IsTriangulated
      (PbcCompletedDerived X (pbcIntegralDatum l E))
      (PbcCompletedDerived Y (pbcIntegralDatum l E))
      _ _ _ _ (rawSupport l E c (R X))
      commShift
      inferInstance inferInstance inferInstance inferInstance
      (inferInstance : ∀ n : ℤ,
        (shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum l E)) n).Additive)
      (inferInstance : ∀ n : ℤ,
        (shiftFunctor (PbcCompletedDerived Y (pbcIntegralDatum l E)) n).Additive)
      inferInstance inferInstance
  towerEvaluation : ∀ n : ℕ,
    strictTower l E c (R X) ⋙
        pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
      compactSupportRestrictedLevel l E c n
  towerTransition : ∀ (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
    (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
        ((strictTower l E c (R X)).obj K) ≫ (towerEvaluation n).hom.app K =
      (towerEvaluation m).hom.app K ≫ compactSupportRestrictedTransition l E c m n h K
  normalized : ∀ K : CondensedERealization.Integral l E X,
    IsNormalizedCoefficientSequence.{u, u} l E Y
      ((systemSupport l E c).obj
        ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)))


/-- Restriction of the actual total-limit functor to the recorded integral categories.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    CondensedERealization.Integral l E X ⥤ CondensedERealization.Integral l E Y :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
      rawSupport l E c (R X))
    (fun K ↦ M.preserves K.obj K.property)

/-- The reconstructed semilinear compact-support system on an integral input.
Source: blueprint proof Steps 2--3
(blueprint: lem-pur-compact-support-condensed-realization). -/
def reconstructedSystem {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (_M : IntegralModel l E c R) :
    CondensedERealization.Integral l E X ⥤ coefficientSequenceDerived.{u, u} l E Y :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
    (purCoefficientModel l E X).functor ⋙ (R X).reduction ⋙
      systemSupport l E c

/-- The limit presentation retains the canonical counit of the coefficient equivalence.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization). -/
def limitPresentation {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    integralSupport l E c R M ⋙
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)) ⋙
        (purCoefficientModel l E Y).functor ≅
      reconstructedSystem l E c R M ⋙ coefficientSequenceLimit.{u, u} l E Y :=
  Functor.isoWhiskerLeft
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
      (purCoefficientModel l E X).functor ⋙ (R X).reduction ⋙
        systemSupport l E c ⋙ coefficientSequenceLimit.{u, u} l E Y)
    (purCoefficientModel l E Y).counitIso

/-- Alpha is the actual reduction/limit counit, preceded by the canonical limit
presentation. Its evaluated adjuncts are therefore the total-limit projections.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization). -/
def alpha {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    integralSupport l E c R M ⋙
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)) ⋙
        (purCoefficientModel l E Y).functor ⋙ (R Y).reduction ⟶
      reconstructedSystem l E c R M :=
  Functor.whiskerRight (limitPresentation l E c R M).hom (R Y).reduction ≫
    Functor.whiskerLeft (reconstructedSystem l E c R M) (R Y).adjunction.counit

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]


/-- Every finite coefficient embedding is continuous for the extended p-adic topology.
Source: Bhatt--Scholze 6.8.1; blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: regard the embedding as a linear map over Q_l. Its source is finite dimensional,
so the finite-dimensional normed-space continuity theorem applies. -/
theorem coefficientEmbedding_continuous (i : E →ₐ[ℚ_[l]] F) : Continuous i := by
  sorry

/-- The coefficient sheaf map is postcomposition by the given field embedding on
continuous functions. Both the source and target retain the scheme coefficient universe.
Source: blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization). -/
def fieldRingMap (i : E →ₐ[ℚ_[l]] F) :
    Profinite.continuousCoefficientRingSheaf E ⟶
      Profinite.continuousCoefficientRingSheaf F :=
  ⟨{ app := fun S ↦ RingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         ((i.toRingHom.compLeftContinuous S.unop
           (coefficientEmbedding_continuous l E F i)).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The same canonical coefficient change on internal ring objects.
Source: blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization). -/
def fieldMap (i : E →ₐ[ℚ_[l]] F) :
    Profinite.continuousCoefficientRingObj E ⟶ Profinite.continuousCoefficientRingObj F :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (fieldRingMap l E F i)

/-- Postcomposition preserves the internal unit and multiplication.
Source: blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the map comes from a morphism of ring sheaves, so it preserves pointwise
multiplication and the constant unit; the forgetful sheaf functor retains these equations. -/
theorem fieldMap_isMonHom (i : E →ₐ[ℚ_[l]] F) : IsMonHom (fieldMap l E F i) := by
  sorry

attribute [instance] fieldMap_isMonHom

/-- Finite coefficient tensor is exact in the original internal-module categories.
Source: blueprint proof Step 6; finite-free coefficient calculus
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: choose a basis of F over E. The coordinate maps are continuous, hence give the
continuous F-valued coefficient ring as a finite free E-valued module. Inverse image
from the point retains that description, and tensor is a finite direct sum. -/
theorem fieldExtension_flat (i : E →ₐ[ℚ_[l]] F) (W : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap (fieldMap l E F i) W)) := by
  sorry

attribute [instance] fieldExtension_flat

/-- Continuity of an embedding into the algebraic closure, with no coefficient-universe
restriction. Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the embedding is Q_l-linear with finite-dimensional source. The usual linear-map
continuity theorem applies even when the target has infinite Q_l dimension. -/
theorem omegaEmbedding_continuous (i : E →ₐ[ℚ_[l]] PadicAlgCl l) : Continuous i := by
  sorry

/-- A continuous E-valued section remains valued in one finite subextension after embedding.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the algebraic image of E is a finite intermediate field of Qbar_l. The value at
every point belongs to this same image. This proves the defining finite-subfield-valued
condition, including on empty profinite test spaces. -/
theorem omegaEmbedding_finiteValued (i : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (S : Profinite.{u}) (a : C(S, E)) :
    (i.toRingHom.compLeftContinuous S (omegaEmbedding_continuous l E i)) a ∈
      PadicAlgCl.finiteIntermediateFieldValued l S := by
  sorry

/-- The actual finite-subfield-valued algebraic-closure coefficient map. It does not
replace Omega by the larger sheaf of all continuous Omega-valued functions.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization). -/
def omegaRingMap (i : E →ₐ[ℚ_[l]] PadicAlgCl l) :
    Profinite.continuousCoefficientRingSheaf E ⟶ Profinite.padicAlgClCondensedRing l :=
  ⟨{ app := fun S ↦ RingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         (((i.toRingHom.compLeftContinuous S.unop (omegaEmbedding_continuous l E i)).codRestrict
           (PadicAlgCl.finiteIntermediateFieldValued l S.unop)
           (omegaEmbedding_finiteValued l E i S.unop)).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The algebraic-closure map on the actual internal ring objects.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization). -/
def omegaMap (i : E →ₐ[ℚ_[l]] PadicAlgCl l) :
    Profinite.continuousCoefficientRingObj E ⟶ Profinite.padicAlgClRingObj.{u} l :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (omegaRingMap l E i)

/-- The finite-valued coefficient embedding is a morphism of internal rings.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: codomain restriction keeps the pointwise ring operations. Forgetting a ring-sheaf
map to its underlying abelian-sheaf map therefore preserves unit and multiplication. -/
theorem omegaMap_isMonHom (i : E →ₐ[ℚ_[l]] PadicAlgCl l) : IsMonHom (omegaMap l E i) := by
  sorry

attribute [instance] omegaMap_isMonHom

/-- Extension to finite-valued algebraic-closure coefficients is flat.
Source: blueprint proof Steps 13--14
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: express the coefficient object as the filtered union of finite intermediate
extensions containing the image of E. Each stage is finite free over E. Tensor commutes
with this filtered colimit; exact filtered colimits of module sheaves give flatness. -/
theorem omegaExtension_flat (i : E →ₐ[ℚ_[l]] PadicAlgCl l) (W : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap (omegaMap l E i) W)) := by
  sorry

attribute [instance] omegaExtension_flat

/-- Identity coefficient embedding induces the identity internal-ring map.
Source: blueprint proof Steps 9--12
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the map is postcomposition on continuous functions. Postcomposition by the
identity fixes every function, and forgetting the ring action preserves that equality. -/
theorem fieldMap_id : fieldMap l E E (AlgHom.id ℚ_[l] E) = 𝟙 _ := by
  sorry

/-- Successive finite coefficient maps compose strictly on internal rings.
Source: blueprint proof Steps 9--12
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: evaluate the maps on every profinite test object and every continuous section.
Both composites are pointwise application of the composed field embedding. Function
extensionality, followed by faithfulness of the ring-sheaf forgetful functor, gives equality. -/
theorem fieldMap_comp (G : Type u) [NormedField G] [NormedAlgebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] G] (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G) :
    fieldMap l E G (j.comp i) = fieldMap l E F i ≫ fieldMap l F G j := by
  sorry

/-- Finite coefficient composition agrees with the original finite-valued closure map.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: every section is postcomposed by the two embeddings in either order. Both
land in the same finite-subfield-valued subring, and subtype extensionality reduces
the equation to equality of these pointwise functions. -/
theorem omegaMap_comp (i : E →ₐ[ℚ_[l]] F) (a : F →ₐ[ℚ_[l]] PadicAlgCl l) :
    omegaMap l E (a.comp i) = fieldMap l E F i ≫ omegaMap l F a := by
  sorry



end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]


/-- Restricting the actual additive total-limit functor is additive.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the integral categories are full additive subcategories. Their inclusion is
faithful, and the underlying map is exactly the additive rawSupport map. -/
theorem integralSupport_additive {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) : (integralSupport l E c R M).Additive := by
  sorry

attribute [instance] integralSupport_additive

/-- Restricting the normalized constant-scalar total-limit action retains R-linearity.
Source: blueprint proof Step 3
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: scalar multiplication in the integral full subcategory is inherited from the
ambient completed module category. Faithfulness of inclusion reduces linearity to
IntegralModel.linear, with precisely the same constant R-sections. -/
theorem integralSupport_linear {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    (integralSupport l E c R M).Linear (PbcIntegralRing l E) := by
  sorry

attribute [instance] integralSupport_linear

/-- The actual raw scalar localization of integral compact support, on localized morphisms.
Source: blueprint proof Steps 4--5; rational transport
(blueprint: lem-pur-compact-support-condensed-realization). -/
def rationalSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M : IntegralModel l E c R) :
    CondensedERealization.Rational l E X ⥤ CondensedERealization.Rational l E Y :=
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E)
    (integralSupport l E c R M)

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [hp : Fact (ringChar k).Prime] [hl : Fact (ringChar k ≠ l)]

/-- The separated finite-type schemes in the coefficient-realization statement are
Noetherian. Source: blueprint proof Step 1
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: Spec(k) is Noetherian and the structure morphism is finite type. Apply the
finite-type-over-Noetherian theorem; separatedness is not needed for this implication. -/
theorem base_noetherian (T : CondensedERealization.Base k) : IsNoetherian T.scheme := by
  sorry

attribute [instance] base_noetherian

/-- The existing finite-type dimension bound, used for the recorded scalar functor.
Source: blueprint proof Step 1; lem-kun-dimension-finite-type
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: finite type over the zero-dimensional field spectrum gives finite Krull dimension.
The published dimension theorem supplies one natural-number upper bound. -/
theorem base_dimension (T : CondensedERealization.Base k) :
    ∃ n : ℕ, topologicalKrullDim T.scheme ≤ n := by
  sorry

include hp hl in
/-- The coefficient prime is a unit in every stalk of a k-scheme.
Source: blueprint proof Step 1
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the positive characteristic of k is prime and differs from l, so the image of l
in k is nonzero. Its inverse maps to an inverse in every local ring of the scheme. -/
theorem base_primeUnit (T : CondensedERealization.Base k) :
    ∀ x : T.scheme, IsUnit (l : T.scheme.presheaf.stalk x) := by
  sorry

/-- The comparison datum at the fixed geometric compactification. The system arrow is
literally the total-limit counit alpha, and the field functor is the archived ambient
proper/open composite. Source: blueprint proof Steps 1--5
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure RealizationAt (D : CondensedERealization.Data l E k)
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f) where
  integral : IntegralModel l E c R
  alpha_isIso : IsIso (alpha l E c R integral)
  field_preserves : ∀ K : CondensedERealization.Ambient E X.scheme,
    boundedConstructible (CondensedERealization.Coefficient E X.scheme) K →
      boundedConstructible (CondensedERealization.Coefficient E Y.scheme)
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj E) c).obj K)
  realization : rationalSupport l E c R integral ⋙ (D.atObject Y).realization.functor ⋙
        (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι ≅
      (D.atObject X).realization.functor ⋙
        (boundedConstructible (CondensedERealization.Coefficient E X.scheme)).ι ⋙
          CondensedRing.rightDerivedLowerShriekOfCompactification
            (Profinite.continuousCoefficientRingObj E) c

end WeilConjectures.CompactSupportCondensedRealization



namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The existing normalized ordinary/derived scalar transport has a unique value.
Its two normalization fields fix sections and the universal derived counit.
Source: Stacks 03EK, 06YY; blueprint proof Steps 7 and 11
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: ordinary pure tensors generate locally, so the tensor field determines the
ordinary isomorphism. The universal left-derived counit determines the derived
isomorphism. The remaining fields are proofs; proof irrelevance gives record equality. -/
theorem scalarModelTransport_subsingleton (W : Scheme.{u}) :
    Subsingleton (OperationScalarTransport l E F i W) := by
  sorry

/-- Existence of the section- and universal-counit-normalized scalar transport.
Source: Stacks 03EK, 06YY; blueprint proof Steps 7 and 11
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the two ordinary scalar models are the same sheafified balanced tensor
construction. The identity on pure tensors gives their natural isomorphism.
Localizing on K-flat representatives gives the derived isomorphism, normalized
by the actual universal tensor counit on every complex. These are exactly the
tensor and counit fields of the recorded OperationScalarTransport interface. -/
theorem scalarModelTransport_nonempty (W : Scheme.{u}) :
    Nonempty (OperationScalarTransport l E F i W) := by
  sorry

/-- The recorded transport, determined uniquely by its tensor and counit fields.
Source: Stacks 03EK, 06YY; blueprint proof Steps 7 and 11
(blueprint: lem-pur-compact-support-condensed-realization). -/
def scalarModelTransport (W : Scheme.{u}) : OperationScalarTransport l E F i W :=
  (scalarModelTransport_nonempty l E F i W).some

/-- The published coefficient-model scalar comparison followed by the recorded
normalized transport from exact scalar extension to its universal K-flat model.
Source: Stacks 03EK, 06YY; blueprint proof Steps 7 and 11
(blueprint: lem-pur-compact-support-condensed-realization). -/
def scalarPresentation (W : Scheme.{u}) :
    pbcEmbeddingAmbientTensor l E F i W ⋙ (purCoefficientModel l F W).functor ≅
      (purCoefficientModel l E W).functor ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i W) :=
  purScalarModel l E F i W ≪≫
    Functor.isoWhiskerLeft (purCoefficientModel l E W).functor
      (scalarModelTransport l E F i W).derived

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The recorded completed integral scalar functor, with the inherited finite-type
bounds. Its comparison with strict Koszul/Roos scalar extension is the published chi.
Source: blueprint proof Step 7; def-weil-integral-scalar-extension
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralScalar (T : CondensedERealization.Base k) :
    CondensedERealization.Integral l E T.scheme ⥤
      CondensedERealization.Integral l F T.scheme :=
  pbcEmbeddingIntegralTensor l E F i T.scheme (base_dimension k T) (base_primeUnit l k T)

/-- Integral reduction into the actual full derived semilinear category.
Source: blueprint proof Steps 2--3
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralReduction (T : CondensedERealization.Base k)
    (R : CoefficientDerivedSystemCalculus.{u, u} l E T.scheme) :
    CondensedERealization.Integral l E T.scheme ⥤
      DerivedCategory (coefficientSequenceModules.{u, u} l E T.scheme) :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
    (purCoefficientModel l E T.scheme).functor ⋙ R.reduction

universe uI uJ uA uB uC uD uS uT vI vJ vA vB vC vD vS vT

/-- Compose the inclusion, coefficient-presentation and reduction comparisons, with
all intermediate categories and functors explicit. This is precisely the three-factor
canonical comparison used below.
Source: blueprint proof Steps 10--11
(blueprint: lem-pur-compact-support-condensed-realization). -/
def pasteReductionComparison
    {I : Type uI} {J : Type uJ} {A : Type uA} {B : Type uB}
    {C : Type uC} {D : Type uD} {S : Type uS} {T : Type uT}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vA} A] [Category.{vB} B]
    [Category.{vC} C] [Category.{vD} D] [Category.{vS} S] [Category.{vT} T]
    (iE : I ⥤ A) (iF : J ⥤ B) (sI : I ⥤ J) (sA : A ⥤ B)
    (mE : A ⥤ C) (mF : B ⥤ D) (sC : C ⥤ D)
    (rE : C ⥤ S) (rF : D ⥤ T) (sS : S ⥤ T)
    (inclusion : sI ⋙ iF ≅ iE ⋙ sA)
    (presentation : sA ⋙ mF ≅ mE ⋙ sC)
    (reduction : sC ⋙ rF ≅ rE ⋙ sS) :
    sI ⋙ iF ⋙ mF ⋙ rF ≅ iE ⋙ mE ⋙ rE ⋙ sS :=
  Functor.isoWhiskerRight inclusion (mF ⋙ rF) ≪≫
    Functor.isoWhiskerLeft iE
      (Functor.isoWhiskerRight presentation rF ≪≫ Functor.isoWhiskerLeft mE reduction)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical full-system balancing comparison for integral scalar extension.
Source: blueprint proof Steps 10--11
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralReductionScalar (T : CondensedERealization.Base k)
    (RE : CoefficientDerivedSystemCalculus.{u, u} l E T.scheme)
    (RF : CoefficientDerivedSystemCalculus.{u, u} l F T.scheme) :
    integralScalar l E F i k T ⋙ integralReduction l F k T RF ≅
      integralReduction l E k T RE ⋙ (systemScalarData l E F i T.scheme).scalar.T := by
  letI : Fact (∃ n : ℕ, topologicalKrullDim T.scheme ≤ n) := ⟨base_dimension k T⟩
  letI : Fact (∀ x : T.scheme, IsUnit (l : T.scheme.presheaf.stalk x)) :=
    ⟨base_primeUnit l k T⟩
  exact pasteReductionComparison
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l F)))
    (integralScalar l E F i k T) (pbcEmbeddingAmbientTensor l E F i T.scheme)
    (purCoefficientModel l E T.scheme).functor (purCoefficientModel l F T.scheme).functor
    (pbcDerivedExtend (completedCoefficientMap l E F i T.scheme))
    RE.reduction RF.reduction (systemScalarData l E F i T.scheme).scalar.T
    (pbcIntegralScalarInclusionIso l E F i T.scheme)
    (scalarPresentation l E F i T.scheme) (reductionScalar l E F i T.scheme RE RF)

/-- Compatibility with alpha is an equality on the entire derived semilinear system,
using the canonical scalar projection and the reduction/limit adjunction balancing.
Source: blueprint proof Steps 10--11
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsIntegralScalarSquare
    (RE : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W)
    (RF : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l F W)
    (X Y : CondensedERealization.Base k) {f : X.scheme ⟶ Y.scheme} (c : Compactification f)
    (ME : IntegralModel l E c RE) (MF : IntegralModel l F c RF)
    (s : integralSupport l E c RE ME ⋙ integralScalar l E F i k Y ≅
      integralScalar l E F i k X ⋙ integralSupport l F c RF MF) : Prop :=
  ∀ K : CondensedERealization.Integral l E X.scheme,
    (integralReduction l F k Y (RF Y.scheme)).map (s.hom.app K) ≫
        (alpha l F c RF MF).app ((integralScalar l E F i k X).obj K) =
      (integralReductionScalar l E F i k Y (RE Y.scheme) (RF Y.scheme)).hom.app
          ((integralSupport l E c RE ME).obj K) ≫
        (systemScalarData l E F i Y.scheme).scalar.T.map ((alpha l E c RE ME).app K) ≫
        (systemProjection l E F i c).app
          ((integralReduction l E k X (RE X.scheme)).obj K) ≫
        (systemSupport l F c).map
          ((integralReductionScalar l E F i k X (RE X.scheme) (RF X.scheme)).inv.app K)

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The section-ring map induced by the actual internal coefficient map.
Source: Stacks 00YV; blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: apply the coefficient morphism to each underlying abelian-sheaf section.
Its internal unit and multiplication equations make this a section-ring homomorphism.
Naturality is the sheaf-map naturality. The specified section functions determine the
map uniquely, so no additional coefficient identification is chosen. -/
theorem sectionFieldMap_existsUnique (W : Scheme.{u}) :
    ∃! d : CondensedERealization.SectionRing E W ⟶ CondensedERealization.SectionRing F W,
      ∀ (U : W.ProEtᵒᵖ) (x : (CondensedERealization.SectionRing E W).obj.obj U),
        HEq (d.hom.app U x) ((coefficientMap (fieldMap l E F i) W).hom.app U x) := by
  sorry

/-- The unique actual map on reconstructed section rings.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization). -/
def sectionFieldMap (W : Scheme.{u}) :
    CondensedERealization.SectionRing E W ⟶ CondensedERealization.SectionRing F W :=
  (sectionFieldMap_existsUnique l E F i W).exists.choose

/-- Coefficient transport of that same section-ring map through the normalized charts.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization). -/
def realizedFieldMap (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :=
  AE.sectionIso.inv ≫ sectionFieldMap l E F i W ≫ AF.sectionIso.hom

/-- The completed/field coefficient square commutes for the specified inclusions.
Source: blueprint proof Step 12; continuous coefficient realizations
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: at every test object, both maps send a completed integral section to its
pointwise image under i. The integral and section chart normalizations identify these
functions. Equality on every section proves the ring-sheaf square. -/
theorem realizedCoefficient_square (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :
    pbcScalarCoefficientMap l E F i W ≫ AF.integralIso.hom ≫ AF.inclusion =
      (AE.integralIso.hom ≫ AE.inclusion) ≫ realizedFieldMap l E F i W AE AF := by
  sorry

/-- The existing section encoding, with the two derived-category Hom sizes explicit.
Source: blueprint proof Step 12; lem-weil-pbc-condensed-e-realization
(blueprint: lem-pur-compact-support-condensed-realization). -/
def encodingDerived (W : Scheme.{u}) (A : CondensedERealization.At l E W) :
    CondensedERealization.Ambient E W ⥤
      DerivedCategory (pbcModules W (rationalCoefficientSheaf l W E)) :=
  letI := A.encodingAdditive
  letI := A.encodingInverseAdditive
  (CondensedERealization.moduleEncoding l E W A.sectionIso).functor.mapDerivedCategory

/-- The derived section encoding remains an equivalence at the displayed Hom sizes.
Source: Stacks 00YV and 06YY; blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the ordinary section encoding is an additive equivalence. Apply its functor
and inverse degreewise to complexes and localize both at quasi-isomorphisms. The
localized ordinary unit and counit give the derived unit and counit, at the two
independent derived-category universes, and their triangle identities descend. -/
theorem encodingDerived_isEquivalence (W : Scheme.{u})
    (A : CondensedERealization.At l E W) :
    (encodingDerived l E W A).IsEquivalence := by
  sorry

attribute [instance] encodingDerived_isEquivalence

/-- The ordinary encoding/restriction square is identity on all module sections.
Source: Stacks 00YV; blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: both encoded module actions are obtained by restricting the same internal
coefficient action. The definition of realizedFieldMap identifies those actions.
The identity section maps are therefore linear, natural and mutually inverse;
sectionwise faithfulness proves uniqueness. -/
theorem encodingRestriction_existsUnique (W : Scheme.{u})
    (AE : CondensedERealization.At l E W) (AF : CondensedERealization.At l F W) :
    ∃! d : Mod.comap (coefficientMap (fieldMap l E F i) W) ⋙
          (CondensedERealization.moduleEncoding l E W AE.sectionIso).functor ≅
        (CondensedERealization.moduleEncoding l F W AF.sectionIso).functor ⋙
          pbcRestrict (realizedFieldMap l E F i W AE AF),
      ∀ (M : Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
        (CondensedERealization.Coefficient F W)) (U : W.ProEtᵒᵖ)
        (x : (((Mod.comap (coefficientMap (fieldMap l E F i) W) ⋙
          (CondensedERealization.moduleEncoding l E W AE.sectionIso).functor).obj M).val.obj U)),
        HEq ((d.hom.app M).val.app U x) x := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact localization of the section-normalized coefficient restriction square.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization). -/
def encodingRestriction (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :
    (Mod.comap (coefficientMap (fieldMap l E F i) W)).mapDerivedCategory ⋙
        encodingDerived l E W AE ≅
      encodingDerived l F W AF ⋙ pbcDerivedRestrict (realizedFieldMap l E F i W AE AF) :=
  letI := AE.encodingAdditive
  letI := AF.encodingAdditive
  Functor.mapDerivedCategorySquareIso
    (F₁ := Mod.comap (coefficientMap (fieldMap l E F i) W))
    (F₂ := (CondensedERealization.moduleEncoding l E W AE.sectionIso).functor)
    (G₁ := (CondensedERealization.moduleEncoding l F W AF.sectionIso).functor)
    (G₂ := pbcRestrict (realizedFieldMap l E F i W AE AF))
    (encodingRestriction_existsUnique l E F i W AE AF).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual scalar/encoding comparison, obtained by the tensor-adjunction mate.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization). -/
def encodingScalarMap (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :
    encodingDerived l E W AE ⋙ pbcDerivedExtend (realizedFieldMap l E F i W AE AF) ⟶
      condensedScalar (fieldMap l E F i) W ⋙ encodingDerived l F W AF :=
  letI := AE.encodingAdditive
  letI := AF.encodingAdditive
  ((mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (fieldMap l E F i) W))
    (pbcDerivedScalarAdjunction (realizedFieldMap l E F i W AE AF))).symm
      (TwoSquare.mk _ (encodingDerived l F W AF) (encodingDerived l E W AE) _
        (encodingRestriction l E F i W AE AF).hom)).natTrans

/-- The normalized encoding scalar mate is invertible.
Source: blueprint proof Step 12; Stacks 06YY
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: encoding is the exact section-module equivalence. On flat K-flat
representatives the mate sends each balanced tensor to the identical tensor under
this equivalence. Its inverse is the inverse balanced tensor map. The universal
scalar counits descend these inverse maps, giving invertibility on all objects. -/
theorem encodingScalarMap_isIso (W : Scheme.{u}) (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) :
    IsIso (encodingScalarMap l E F i W AE AF) := by
  sorry

attribute [instance] encodingScalarMap_isIso

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual coefficient-extension comparison on integral lattices, descended through
the fully faithful field encoding. All its factors are specified tensor comparisons.
Source: blueprint proof Step 12
(blueprint: lem-pur-compact-support-condensed-realization). -/
def latticeScalar (T : CondensedERealization.Base k)
    (AE : CondensedERealization.At l E T.scheme) (AF : CondensedERealization.At l F T.scheme) :
    integralScalar l E F i k T ⋙
        pbcRationalization T.scheme (pbcIntegralDatum l F) (pbcUniformizer l F) ⋙
        AF.realization.functor ⋙
        (boundedConstructible (CondensedERealization.Coefficient F T.scheme)).ι ≅
      pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        AE.realization.functor ⋙
        (boundedConstructible (CondensedERealization.Coefficient E T.scheme)).ι ⋙
        (condensedScalar (fieldMap l E F i) T.scheme) :=
  by
  letI := AE.encodingAdditive
  letI := AF.encodingAdditive
  letI := AF.encodingInverseAdditive
  exact Functor.fullyFaithfulCancelRight
    (encodingDerived l F T.scheme AF)
    (Functor.isoWhiskerLeft (integralScalar l E F i k T) AF.scalarExtension ≪≫
      Functor.isoWhiskerLeft
        (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)))
        (PurCompactSupport.tensorSquare (pbcScalarCoefficientMap l E F i T.scheme)
          (realizedFieldMap l E F i T.scheme AE AF) (AE.integralIso.hom ≫ AE.inclusion)
          (AF.integralIso.hom ≫ AF.inclusion) (realizedCoefficient_square l E F i T.scheme AE AF))
      ≪≫ Functor.isoWhiskerRight AE.scalarExtension.symm
        (pbcDerivedExtend (realizedFieldMap l E F i T.scheme AE AF)) ≪≫
      Functor.isoWhiskerLeft
        (pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
          AE.realization.functor ⋙
          (boundedConstructible (CondensedERealization.Coefficient E T.scheme)).ι)
        (asIso (encodingScalarMap l E F i T.scheme AE AF)))

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)


/-- The actual finite condensed scalar functor.
Source: blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization). -/
abbrev fieldScalar (W : Scheme.{u}) :=
  condensedScalar (fieldMap l E F i) W

/-- The actual finite-valued algebraic-closure scalar functor.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization). -/
abbrev omegaScalar (a : E →ₐ[ℚ_[l]] PadicAlgCl l) (W : Scheme.{u}) :=
  condensedScalar (omegaMap l E a) W

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- Simultaneous reconstruction and field realization for one coefficient field.
The reduction and realization data are the recorded dependency data; the support
functors retain the fixed geometric compactification.
Source: blueprint proof Steps 1--5
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure CoefficientData where
  realization : CondensedERealization.Data l E k
  reduction : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W
  atCompactification : ∀ (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f),
    RealizationAt l E k realization reduction X Y f c

/-- The rationalized coefficient square, with exactly the specified scalar and realization
maps. Packaging this equation keeps generated comparison-record declarations small.
Source: blueprint proof Steps 7--12
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsFiniteRationalSquare (A : CoefficientData l E k) (B : CoefficientData l F k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f)
    (comparison :
    integralSupport l E c A.reduction (A.atCompactification X Y f c).integral ⋙
        integralScalar l E F i k Y ≅
      integralScalar l E F i k X ⋙
        integralSupport l F c B.reduction (B.atCompactification X Y f c).integral) : Prop :=
  ∀ K : CondensedERealization.Integral l E X.scheme,
    ((B.realization.atObject Y).realization.functor ⋙
      (boundedConstructible (CondensedERealization.Coefficient F Y.scheme)).ι).map
        ((pbcRationalization Y.scheme (pbcIntegralDatum l F) (pbcUniformizer l F)).map
          (comparison.hom.app K)) ≫
        (B.atCompactification X Y f c).realization.hom.app
          (ScalarLocalization.mk ((integralScalar l E F i k X).obj K)) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj F) c).map
            ((latticeScalar l E F i k X
              (A.realization.atObject X) (B.realization.atObject X)).hom.app K) =
      (latticeScalar l E F i k Y
        (A.realization.atObject Y) (B.realization.atObject Y)).hom.app
          ((integralSupport l E c A.reduction
            (A.atCompactification X Y f c).integral).obj K) ≫
        (fieldScalar l E F i Y.scheme).map
          ((A.atCompactification X Y f c).realization.hom.app (ScalarLocalization.mk K)) ≫
        (condensedProjection (fieldMap l E F i) c).app
          (((A.realization.atObject X).realization.functor.obj (ScalarLocalization.mk K)).obj)

/-- The finite integral comparison, with its whole-system and rationalized squares.
These equations fix its normalization by the actual coefficient projection mate.
Source: blueprint proof Steps 7--12
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure FiniteComparison (A : CoefficientData l E k) (B : CoefficientData l F k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f) where
  comparison :
    integralSupport l E c A.reduction (A.atCompactification X Y f c).integral ⋙
        integralScalar l E F i k Y ≅
      integralScalar l E F i k X ⋙
        integralSupport l F c B.reduction (B.atCompactification X Y f c).integral
  reduction : IsIntegralScalarSquare l E F i k A.reduction B.reduction X Y c
    (A.atCompactification X Y f c).integral
    (B.atCompactification X Y f c).integral comparison
  rationalization : IsFiniteRationalSquare l E F i k A B X Y f c comparison


/-- Finite field extension preserves the indicated constructible subcategory.
Source: blueprint proof Step 6; finite free coefficient extension
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: finite extension is finite free and exact on modules. On each constructible
stratum it carries a finite presentation to its scalar-extended presentation and
commutes with the pro-etale trivialization. Exactness preserves the common finite
cohomological bounds, giving the same bounded constructibility predicate. -/
theorem fieldScalar_preserves (W : Scheme.{u}) (K : CondensedERealization.Constructible E W) :
    boundedConstructible (CondensedERealization.Coefficient F W)
      ((fieldScalar l E F i W).obj K.obj) := by
  sorry

/-- Extension to the finite-valued closure preserves bounded constructibility.
Source: blueprint proof Steps 13--14; finite-coefficient two-colimit
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: scalar extension is the filtered colimit of finite free coefficient changes
and hence exact. Scalar-extending each finite presentation on the same finite
stratification preserves local finite presentation and the cohomological bounds.
The coefficient ring is the finite-subfield-valued ring throughout. -/
theorem omegaScalar_preserves (a : E →ₐ[ℚ_[l]] PadicAlgCl l) (W : Scheme.{u})
    (K : CondensedERealization.Constructible E W) :
    boundedConstructible (padicAlgClRingObj W l) ((omegaScalar l E a W).obj K.obj) := by
  sorry

/-- Finite projection is invertible on the indicated constructible domain.
Source: blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: finite extension coefficients are finite free. The proper comparison is its
counit transpose and identifies with a finite direct-sum comparison. Paste it with
the open tensor comparison, normalized by the open unit. Both are invertible. -/
theorem finiteProjection_isIso (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Constructible E X.scheme) :
    IsIso ((condensedProjection (fieldMap l E F i) c).app K.obj) := by
  sorry

/-- Closure projection is the same canonical map, on the bounded constructible domain.
Source: blueprint proof Steps 13--14
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: express the finite-valued closure coefficient as the filtered colimit of finite
extensions containing the image of E. Use simultaneous coefficient complexes with a
common lower bound. Exact open extension commutes with this colimit. Bounded-below
qcqs proper-image continuity identifies the colimit of the finite projection maps
with this precise counit transpose. Each finite projection is invertible. -/
theorem omegaProjection_isIso (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Constructible E X.scheme) :
    IsIso ((condensedProjection (omegaMap l E a) c).app K.obj) := by
  sorry

/-- The original closure proper/open composite preserves bounded constructibility.
Source: blueprint proof Step 14
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: descend the object to a finite coefficient field by the filtered two-colimit
statement. The closure projection identifies its image with scalar extension of the
finite-field compact-support image. That image and its scalar extension are bounded
constructible. Common-stage descent of arrows ensures independence and naturality. -/
theorem omegaSupport_preserves (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X.scheme) Ab.{u + 1})
      (padicAlgClRingObj X.scheme l)))
    (hK : boundedConstructible (padicAlgClRingObj X.scheme l) K) :
    boundedConstructible (padicAlgClRingObj Y.scheme l)
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj.{u} l) c).obj K) := by
  sorry

end WeilConjectures.CompactSupportCondensedRealization





namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]


/-- The compactification opens have the finiteness needed for the whole-system mate.
Source: blueprint proof Step 15; finite-type over Noetherian schemes
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the middle scheme is proper over the Noetherian finite-type target, hence
Noetherian. Every open immersion into a Noetherian scheme is quasi-compact. -/
theorem compactification_open_quasiCompact (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f) :
    QuasiCompact c.i := by
  sorry

universe uA uB uC uD vA vB vC vD

/-- Paste an open-unit transpose with the proper-image compositor in the functor category.
Source: blueprint proof Step 15; Stacks 07A7 and 0F7B
(blueprint: lem-pur-compact-support-condensed-realization). -/
def pasteRefinement
    {C : Type uA} {D : Type uB} {S : Type uC} {T : Type uD}
    [Category.{vA} C] [Category.{vB} D] [Category.{vC} S] [Category.{vD} T]
    (jd : C ⥤ S) (jc : C ⥤ D) (r : D ⥤ S) (g : S ⥤ T) (h : D ⥤ T)
    (a : jd ⟶ jc ⋙ r) (b : r ⋙ g ≅ h) : jd ⋙ g ⟶ jc ⋙ h :=
  Functor.whiskerRight a g ≫ (Functor.associator jc r g).hom ≫
    Functor.whiskerLeft jc b.hom

attribute [local semireducible] WeilConjectures.integralCoefficientCommRingSheaf

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Whole-system refinement is the intrinsic proper/open mate, followed by the
proper compositor. No levelwise arrows are assembled into a derived-system map.
Source: blueprint proof Step 15; Stacks 0F7B
(blueprint: lem-pur-compact-support-condensed-realization). -/
def systemRefinement (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d) :
    systemSupport l E d ⟶ systemSupport l E c := by
  letI := compactification_open_quasiCompact k X Y f c
  letI := compactification_open_quasiCompact k X Y f d
  unfold systemSupport
  let transition :
      SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) d.i ⟶
        SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) c.i ⋙
          SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) r.hom :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight
        (SemilinearProperOpen.sId (quotientRings l E) (quotientMaps l E) X.scheme).inv
        (SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) d.i) ≫
      SemilinearProperOpen.gamma (quotientRings l E) (quotientMaps l E)
        c.i (𝟙 X.scheme) r.hom d.i (r.i_hom.trans (Category.id_comp _).symm)
  let push :
      SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) r.hom ⋙
          SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) d.g ≅
        SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) c.g :=
    SemilinearProperOpen.sComp (quotientRings l E) (quotientMaps l E) r.hom d.g ≪≫
      eqToIso (congrArg
        (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E)) r.hom_g)
  exact pasteRefinement
    (SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) d.i)
    (SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) c.i)
    (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) r.hom)
    (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) d.g)
    (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) c.g)
    transition push

attribute [local irreducible] WeilConjectures.integralCoefficientCommRingSheaf

/-- The actual limit of the whole-system refinement, in the completed presentation.
Source: blueprint proof Step 15
(blueprint: lem-pur-compact-support-condensed-realization). -/
def rawRefinement (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d) :
    rawSupport l E d (A.reduction X.scheme) ⟶ rawSupport l E c (A.reduction X.scheme) :=
  Functor.whiskerRight
    (Functor.whiskerLeft ((purCoefficientModel l E X.scheme).functor ⋙
      (A.reduction X.scheme).reduction) (systemRefinement l E k X Y f r))
    (coefficientSequenceDerivedRestriction.{u, u} l E Y.scheme ⋙
      coefficientConstantTowerLimit.{u, u} l E Y.scheme ⋙
        (purCoefficientModel l E Y.scheme).inverse)

/-- Restrict an actual natural transformation to a full subcategory of its target.
Source: blueprint proof Step 15; Mathlib ObjectProperty.lift
(blueprint: lem-pur-compact-support-condensed-realization). -/
def liftSupportTransformation
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    (P : ObjectProperty D) (F G : C ⥤ D)
    (hF : ∀ K, P (F.obj K)) (hG : ∀ K, P (G.obj K)) (a : F ⟶ G) :
    P.lift F hF ⟶ P.lift G hG where
  app K := ObjectProperty.homMk (a.app K)
  naturality _K _L v := ObjectProperty.hom_ext _ (a.naturality v)

/-- Restriction of that actual limit map to the full integral categories.
Source: blueprint proof Step 15
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralRefinement (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d) :
    integralSupport l E d A.reduction (A.atCompactification X Y f d).integral ⟶
      integralSupport l E c A.reduction (A.atCompactification X Y f c).integral :=
  liftSupportTransformation
    (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) ⋙
      rawSupport l E d (A.reduction X.scheme))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) ⋙
      rawSupport l E c (A.reduction X.scheme))
    (fun K ↦ (A.atCompactification X Y f d).integral.preserves K.obj K.property)
    (fun K ↦ (A.atCompactification X Y f c).integral.preserves K.obj K.property)
    (Functor.whiskerLeft
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)))
      (rawRefinement l E k A X Y f r))

/-- The refinement squares for reconstruction and field realization, before any
coefficient extension is made. These are equations of the actual whole-system maps.
Source: blueprint proof Steps 15--16
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure RefinementCoherence (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] {c d : Compactification f} (r : c.Refinement d) : Prop where
  invertible : IsIso (integralRefinement l E k A X Y f r)
  field_invertible : IsIso (fieldRefinement (Profinite.continuousCoefficientRingObj E) r)
  reduction : ∀ K : CondensedERealization.Integral l E X.scheme,
    (integralReduction l E k Y (A.reduction Y.scheme)).map
        ((integralRefinement l E k A X Y f r).app K) ≫
        (alpha l E c A.reduction (A.atCompactification X Y f c).integral).app K =
      (alpha l E d A.reduction (A.atCompactification X Y f d).integral).app K ≫
        (systemRefinement l E k X Y f r).app
          ((integralReduction l E k X (A.reduction X.scheme)).obj K)
  realization : ∀ K : CondensedERealization.Integral l E X.scheme,
    ((A.realization.atObject Y).realization.functor ⋙
      (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι).map
        ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          ((integralRefinement l E k A X Y f r).app K)) ≫
        (A.atCompactification X Y f c).realization.hom.app (ScalarLocalization.mk K) =
      (A.atCompactification X Y f d).realization.hom.app (ScalarLocalization.mk K) ≫
        (fieldRefinement (Profinite.continuousCoefficientRingObj E) r).app
          ((A.realization.atObject X).realization.functor.obj (ScalarLocalization.mk K))

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime]
  (E F G : Type u) [NormedField E] [NormedField F] [NormedField G]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F] [NormedAlgebra ℚ_[l] G]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] [FiniteDimensional ℚ_[l] G]
  (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The inherited integral tensor associator is the published ambient tensor associator.
Source: blueprint proof Steps 9--12; prop-weil-pbc-scalar-extension
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralScalarComp (T : CondensedERealization.Base k) :
    integralScalar l E F i k T ⋙ integralScalar l F G j k T ≅
      integralScalar l E G (j.comp i) k T :=
  NatIso.ofComponents
    (F := integralScalar l E F i k T ⋙ integralScalar l F G j k T)
    (G := integralScalar l E G (j.comp i) k T)
    (fun K ↦
      ObjectProperty.isoMk _
        (X := (integralScalar l E F i k T ⋙ integralScalar l F G j k T).obj K)
        (Y := (integralScalar l E G (j.comp i) k T).obj K)
        ((pbcAmbientScalarComp l E F G i j T.scheme).app K.obj))
    (fun v ↦ by
      ext
      exact (pbcAmbientScalarComp l E F G i j T.scheme).hom.naturality v.hom)

/-- The integral identity scalar comparison is the actual tensor unit.
Source: blueprint proof Steps 9--12; prop-weil-pbc-scalar-extension
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralScalarId (T : CondensedERealization.Base k) :
    integralScalar l E E (AlgHom.id ℚ_[l] E) k T ≅ 𝟭 _ :=
  NatIso.ofComponents
    (F := integralScalar l E E (AlgHom.id ℚ_[l] E) k T) (G := 𝟭 _)
    (fun K ↦
      ObjectProperty.isoMk _
        (X := (integralScalar l E E (AlgHom.id ℚ_[l] E) k T).obj K) (Y := K)
        ((pbcEmbeddingAmbientUnit l E T.scheme).app K.obj))
    (fun v ↦ by
      ext
      exact (pbcEmbeddingAmbientUnit l E T.scheme).hom.naturality v.hom)

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The actual bounded constructible predicate is closed under all ambient shifts.
Source: archived ProEtaleModule/DerivedCategory.lean, cohomological definition;
blueprint proof Step 17 (blueprint: lem-pur-compact-support-condensed-realization).
Proof: shifting reindexes the cohomology sheaves by an integer and translates the
finite vanishing interval. The cohomology shift isomorphism preserves the existing
local finite-presentation condition on every stratum, so constructibility is unchanged.
This uses no kernel or extension closure assertion for arbitrary coefficient rings. -/
theorem fieldConstructible_shiftStable (E : Type u) [NormedField E] (W : Scheme.{u}) :
    (boundedConstructible (CondensedERealization.Coefficient E W)).IsStableUnderShift ℤ := by
  sorry

attribute [local instance] fieldConstructible_shiftStable

/-- Shift compatibility includes the universal coefficient counits and the
scalar-extension normalization of the realization, fixing the induced comparisons.
The rational shifts are exactly the recorded tensor-localization shifts.
Source: blueprint proof Step 17; lem-weil-pbc-derived-adjunction-shift
(blueprint: lem-pur-compact-support-condensed-realization). -/
def shiftCoherentClauses (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    [IsNoetherian X.scheme] [IsNoetherian Y.scheme]
    [Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y.scheme ≤ n)]
    [Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))]
    [Fact (∀ y : Y.scheme, IsUnit (l : Y.scheme.presheaf.stalk y))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))]
    (c : Compactification f)
    (sI : (integralSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ)
    (sQ : (rationalSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ)
    (sX : (A.realization.atObject X).realization.functor.CommShift ℤ)
    (sY : (A.realization.atObject Y).realization.functor.CommShift ℤ)
    (sRX : (A.reduction X.scheme).reduction.CommShift ℤ)
    (sRY : (A.reduction Y.scheme).reduction.CommShift ℤ)
    (sLX : (coefficientSequenceLimit l E X.scheme).CommShift ℤ)
    (sLY : (coefficientSequenceLimit l E Y.scheme).CommShift ℤ)
    (sPX : (purCoefficientModel l E X.scheme).functor.CommShift ℤ)
    (sPY : (purCoefficientModel l E Y.scheme).functor.CommShift ℤ)
    (sS : (systemSupport l E c).CommShift ℤ)
    (sVX : (pbcRationalization X.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)).CommShift ℤ)
    (sVY : (pbcRationalization Y.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)).CommShift ℤ) : Prop := by
  letI := base_noetherian k X
  letI := base_noetherian k Y
  letI := pbcIntegralTriangulated l E X.scheme (base_dimension k X) (base_primeUnit l k X)
  letI := pbcIntegralTriangulated l E Y.scheme (base_dimension k Y) (base_primeUnit l k Y)
  letI := pbcRationalShift l E X.scheme (base_dimension k X) (base_primeUnit l k X)
  letI := pbcRationalShift l E Y.scheme (base_dimension k Y) (base_primeUnit l k Y)
  letI := (pbcRationalTriangulationData l E X.scheme
    (base_dimension k X) (base_primeUnit l k X)).choose_spec.choose_spec.2.choose_spec.choose
  letI := (pbcRationalTriangulationData l E Y.scheme
    (base_dimension k Y) (base_primeUnit l k Y)).choose_spec.choose_spec.2.choose_spec.choose
  letI := (A.realization.atObject X).encodingAdditive
  letI := (A.realization.atObject Y).encodingAdditive
  letI := (A.realization.atObject X).encodingInverseAdditive
  letI := (A.realization.atObject Y).encodingInverseAdditive
  letI := sI
  letI := sQ
  letI := sX
  letI := sY
  letI := sRX
  letI := sRY
  letI := sLX
  letI := sLY
  letI := sPX
  letI := sPY
  letI := sS
  letI := sVX
  letI := sVY
  letI : (reconstructedSystem l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ := by
    unfold reconstructedSystem
    infer_instance
  letI : (CondensedERealization.moduleEncoding l E X.scheme
      (A.realization.atObject X).sectionIso).mapDerivedCategory.functor.CommShift ℤ :=
    inferInstanceAs ((CondensedERealization.moduleEncoding l E X.scheme
      (A.realization.atObject X).sectionIso).functor.mapDerivedCategory.CommShift ℤ)
  letI : (CondensedERealization.moduleEncoding l E Y.scheme
      (A.realization.atObject Y).sectionIso).mapDerivedCategory.functor.CommShift ℤ :=
    inferInstanceAs ((CondensedERealization.moduleEncoding l E Y.scheme
      (A.realization.atObject Y).sectionIso).functor.mapDerivedCategory.CommShift ℤ)
  let I := integralSupport l E c A.reduction
    (A.atCompactification X Y f c).integral
  let Q := rationalSupport l E c A.reduction
    (A.atCompactification X Y f c).integral
  let hI : Prop := I.IsTriangulated
  let hRX : Prop := NatTrans.CommShift (A.reduction X.scheme).adjunction.counit ℤ
  let hRY : Prop := NatTrans.CommShift (A.reduction Y.scheme).adjunction.counit ℤ
  let hLimit : Prop := NatTrans.CommShift
    (limitPresentation l E c A.reduction (A.atCompactification X Y f c).integral).hom ℤ
  let hAlpha : Prop := NatTrans.CommShift
    (alpha l E c A.reduction (A.atCompactification X Y f c).integral) ℤ
  let hSX : Prop := NatTrans.CommShift (A.realization.atObject X).scalarExtension.hom ℤ
  let hSY : Prop := NatTrans.CommShift (A.realization.atObject Y).scalarExtension.hom ℤ
  let hReal : Prop := NatTrans.CommShift (A.atCompactification X Y f c).realization.hom ℤ
  exact hI ∧ hRX ∧ hRY ∧ hLimit ∧ hAlpha ∧ hSX ∧ hSY ∧ hReal ∧
        ∀ (K : CondensedERealization.Integral l E X.scheme) (n : ℤ),
          HEq ((Q.commShiftIso n).hom.app
              (ScalarLocalization.mk K))
            ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
              (I.commShiftIso n).hom.app K)

/-- Shift structures of the support, realization, reduction and their constituent functors,
with the stipulated counit and scalar comparison equations.
Source: blueprint proof Step 17; Bhatt--Scholze 6.8.15
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure ShiftCoherentWitness (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    [IsNoetherian X.scheme] [IsNoetherian Y.scheme]
    [Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y.scheme ≤ n)]
    [Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))]
    [Fact (∀ y : Y.scheme, IsUnit (l : Y.scheme.presheaf.stalk y))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))]
    (c : Compactification f) where
  sI : (integralSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ
  sQ : (rationalSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ
  sX : (A.realization.atObject X).realization.functor.CommShift ℤ
  sY : (A.realization.atObject Y).realization.functor.CommShift ℤ
  sRX : (A.reduction X.scheme).reduction.CommShift ℤ
  sRY : (A.reduction Y.scheme).reduction.CommShift ℤ
  sLX : (coefficientSequenceLimit l E X.scheme).CommShift ℤ
  sLY : (coefficientSequenceLimit l E Y.scheme).CommShift ℤ
  sPX : (purCoefficientModel l E X.scheme).functor.CommShift ℤ
  sPY : (purCoefficientModel l E Y.scheme).functor.CommShift ℤ
  sS : (systemSupport l E c).CommShift ℤ
  sVX : (pbcRationalization X.scheme (pbcIntegralDatum l E)
    (pbcUniformizer l E)).CommShift ℤ
  sVY : (pbcRationalization Y.scheme (pbcIntegralDatum l E)
    (pbcUniformizer l E)).CommShift ℤ
  clauses : shiftCoherentClauses l k E A X Y f c sI sQ sX sY sRX sRY
    sLX sLY sPX sPY sS sVX sVY

/-- Existence of compatible integral, rational, realization and reduction shifts.
Source: blueprint proof Step 17; Bhatt--Scholze 6.8.15
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsShiftCoherent (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f) : Prop :=
  letI := base_noetherian k X
  letI := base_noetherian k Y
  letI : Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) := ⟨base_dimension k X⟩
  letI : Fact (∃ n : ℕ, topologicalKrullDim Y.scheme ≤ n) := ⟨base_dimension k Y⟩
  letI : Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x)) :=
    ⟨base_primeUnit l k X⟩
  letI : Fact (∀ y : Y.scheme, IsUnit (l : Y.scheme.presheaf.stalk y)) :=
    ⟨base_primeUnit l k Y⟩
  letI := pbcIntegralTriangulated l E X.scheme (base_dimension k X) (base_primeUnit l k X)
  letI := pbcIntegralTriangulated l E Y.scheme (base_dimension k Y) (base_primeUnit l k Y)
  Nonempty (ShiftCoherentWitness l k E A X Y f c)

/-- Simultaneous compact-support realizations and their specified finite-coefficient
and refinement composition laws. All functors and refinement arrows used below were
constructed above from the recorded dependency operations.
Source: blueprint proof Steps 1--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure ComparisonFamilyCore where
  coefficient : ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], CoefficientData l E k
  shifts : ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f),
    IsShiftCoherent l k E (coefficient E) X Y f c
  finite : ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f),
    FiniteComparison l E F i k (coefficient E) (coefficient F) X Y f c
  refinement : ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d),
    RefinementCoherence l E k (coefficient E) X Y f r

/-- Scalar identity for the specified integral coefficient comparisons.
Source: blueprint proof Steps 9--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsScalarIdentity (C : ComparisonFamilyCore l k) : Prop :=
  ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Integral l E X.scheme),
    (C.finite E E (AlgHom.id ℚ_[l] E) X Y f c).comparison.hom.app K ≫
        (integralSupport l E c (C.coefficient E).reduction
          ((C.coefficient E).atCompactification X Y f c).integral).map
            ((integralScalarId l E k X).hom.app K) =
      (integralScalarId l E k Y).hom.app
        ((integralSupport l E c (C.coefficient E).reduction
          ((C.coefficient E).atCompactification X Y f c).integral).obj K)

/-- Scalar composition for the specified integral coefficient comparisons.
Source: blueprint proof Steps 9--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsScalarComposition (C : ComparisonFamilyCore l k) : Prop :=
  ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F]
    (G : Type u) [NormedField G] [NormedAlgebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] G]
    (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Integral l E X.scheme),
    (integralScalar l F G j k Y).map
        ((C.finite E F i X Y f c).comparison.hom.app K) ≫
        (C.finite F G j X Y f c).comparison.hom.app ((integralScalar l E F i k X).obj K) ≫
        (integralSupport l G c (C.coefficient G).reduction
          ((C.coefficient G).atCompactification X Y f c).integral).map
            ((integralScalarComp l E F G i j k X).hom.app K) =
      (integralScalarComp l E F G i j k Y).hom.app
          ((integralSupport l E c (C.coefficient E).reduction
            ((C.coefficient E).atCompactification X Y f c).integral).obj K) ≫
        (C.finite E G (j.comp i) X Y f c).comparison.hom.app K

/-- Scalar refinement for the specified integral coefficient comparisons.
Source: blueprint proof Steps 9--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsScalarRefinement (C : ComparisonFamilyCore l k) : Prop :=
  ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d)
    (K : CondensedERealization.Integral l E X.scheme),
    (integralScalar l E F i k Y).map
        ((integralRefinement l E k (C.coefficient E) X Y f r).app K) ≫
        (C.finite E F i X Y f c).comparison.hom.app K =
      (C.finite E F i X Y f d).comparison.hom.app K ≫
        (integralRefinement l F k (C.coefficient F) X Y f r).app
          ((integralScalar l E F i k X).obj K)

/-- The simultaneous family with its identity, coefficient-tower and refinement equations.
Source: blueprint proof Steps 1--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure ComparisonFamily extends ComparisonFamilyCore l k where
  scalar_identity : IsScalarIdentity l k toComparisonFamilyCore
  scalar_composition : IsScalarComposition l k toComparisonFamilyCore
  scalar_refinement : IsScalarRefinement l k toComparisonFamilyCore

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- Identity refinement is the identity on the full derived semilinear system.
Source: blueprint proof Step 15; Stacks 0F7B
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the identity proper adjunction has identity unit and counit. The open
restriction normalization is the original unit; its Hom bijection identifies the
proper/open mate with the identity. The normalized proper compositor cancels it. -/
theorem systemRefinement_id (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f) :
    systemRefinement l E k X Y f (Compactification.Refinement.id c) = 𝟙 _ := by
  sorry

/-- Refinement composition holds before evaluation and before total limit.
Source: blueprint proof Step 15; Stacks 07A7 and 0F7B
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: paste the two clopen-section open squares. Their original-open unit is the
unit of the composite square; the two-stage and composite transposes agree by the
proper adjunction triangles. The proper compositors satisfy their mate cocycle,
so uniqueness in the open Hom bijection gives the full-system equality. -/
theorem systemRefinement_comp (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    systemRefinement l E k X Y f (r.comp s) =
      systemRefinement l E k X Y f s ≫ systemRefinement l E k X Y f r := by
  sorry

/-- Closure refinement is invertible on exactly the bounded constructible domain.
Source: blueprint proof Steps 15--16; finite-coefficient descent
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: descend the input and the refinement diagram to one finite coefficient field.
The finite refinement square agrees with the intrinsic clopen-section mate on the
whole system. Proper continuity and exact open extension identify its closure scalar
extension with the displayed original closure refinement. Scalar extension preserves
its inverse, proving invertibility independently of the descent choice. -/
theorem omegaRefinement_isIso (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d) :
    IsIso (fieldRefinement (Profinite.padicAlgClRingObj.{u} l) r) := by
  sorry

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures

/-- Compact-support reconstruction and condensed coefficient realization.
Source: blueprint sk-thm-purity-transport, Steps 2--3; Bhatt--Scholze 6.7.2,
6.7.14--6.7.17 and 6.8.14--6.8.15
(blueprint: lem-pur-compact-support-condensed-realization).
Proof:
1. Ordinary completed-coefficient proper/open support is bounded constructible and
complete, by finite cohomological dimension, finite-level finiteness and strict-limit
compatibility. Identify its reduction with the geometric full-system support through
proper coefficient transpose and the unit-normalized open tensor comparison.
2. Adjunction of reduction and total limit gives the unit comparison to the actual
strict-tower limit. Normalized-system reconstruction makes it invertible. Its counit
is alpha; the triangle identity identifies every evaluated component with the
original total-limit projection, together with all transitions and scalar actions.
3. Rationalize the inverse unit comparison, apply the coefficient-realization
equivalence, then the proper comparison and the normalized open comparison. This
constructs the natural isomorphism a without deriving the nonexact composite anew.
4. For finite coefficient extension, the proper coefficient mate is a finite direct-
sum comparison and the open factor is the exact scalar comparison. Their composite
is the specified projection and is invertible on constructible inputs.
5. Completed integral scalar extension is finite free; the canonical Roos and tensor
comparison commutes with total limit. If t=u v^e, use the cofinal levels en on the
larger ring. Do not identify t^n with v^n or assume flatness of the finite quotients.
6. Prove the coefficient square on the whole strict system using the actual mates,
then take its limit. The adjunction triangle identities give the alpha square. The
canonical completed-to-field ring square and tensor counits give the rationalized
square with a and the original condensed coefficient projection.
7. Identity and successive coefficient comparisons satisfy the tensor cocycle by
ordinary unit/counit pasting, then K-flat localization and strict Roos cofinality.
8. For the finite-valued closure coefficient, descend objects and arrows to a common
finite field. Bounded-below qcqs proper-image continuity and exact open extension
identify the filtered colimit of the finite projections with the original closure
projection. This proves invertibility and constructible preservation.
9. For a proper compactification refinement, restriction over the open identifies a
clopen section. Extension by zero is the input there and zero on the complement.
This gives the intrinsic whole-system proper/open refinement and its identity and
composition laws. Limits, alpha, a and coefficient changes commute with these same
maps by the normalized mate squares; the same argument passes to the closure.
10. All maps are natural in complexes and localized morphisms. Universal derived
units and counits fix their shift comparisons; faithful inclusions and scalar
localization preserve these equations and their zero and addition coherence.
The dependencies used at these steps are exactly those in the node's proof plan. -/
theorem compactSupport_condensedRealization (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] :
    Nonempty (CompactSupportCondensedRealization.ComparisonFamily l k) := by
  sorry

end WeilConjectures
