/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.CompletedProjectionCoherence
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Paper.IntegralTensorReductionTowerComparison
import Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit
import Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas
import Sheaf.SixFunctors.CompactSupportProperImageTower
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.SixFunctors.IntegralOpenReductionComparison
import Sheaf.Paper.OpenFiniteConstructibilityInterval
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.SixFunctors.OpenFactorTensorModel
public import Sheaf.Paper.CompletedOperationTowerSubstitution

/-!
# Completed compactification realization without a Tor bound

Source: blueprint main-20261015, sk-prop-sf-pf-reduction, proof of
lem-fix-operation-reduction, paragraph 2 and final paragraph
(blueprint: lem-fix-compactification-completed-realization).

The main statement is `completedRealization`. Its helper definitions retain the
actual completion units, finite counit projections and derived strict-tower maps.
`supportTower` and `supportEvaluation` alias the recorded compact-support choices.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactificationCompletedRealization
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The ordered augmentation of the tensor argument of compact support: first
complete tensor, then insert the ordinary-to-completed pullback comparison.
Source: node proof steps 7--10
(blueprint: lem-fix-compactification-completed-realization). -/
def argumentUnit (a : OpenFactorCoherence.Tensor l E X) (b : OpenFactorCoherence.Pull l E f)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (L : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
  (a.chi l E).app (K, (pull (completed l E) f).obj L) ≫
    (integralCompletedTensor.{u, u} l E X).map (Prod.mkHom (𝟙 K) ((b.unit l E).app L))

/-- The finite comparison at exponent n+1 is precisely proper perfect-coefficient
projection followed by proper image of the normalized open tensor comparison.
The outer coordinates are the published scalar-reduction identifications.
Source: Stacks 0943, 0E8I; node proof step 6
(blueprint: lem-fix-compactification-completed-realization). -/
def orderedReduction (n : ℕ) (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
  let a := reduction l E (n + 1) (Nat.le_add_left 1 n)
  (properComparison a c.g).app ((openExtension (completed l E) c.i).mapDerivedCategory.obj K) ≫
    (push (finite l E (n + 1) (Nat.le_add_left 1 n)) c.g).map
      ((openComparison a c.i).app K)


/-- The source of the completed compact-support projection.
Source: blueprint sk-prop-sf-pf-reduction, final paragraph
(blueprint: lem-fix-compactification-completed-realization). -/
abbrev projectionSource (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (L : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
  (integralCompletedTensor.{u, u} l E Y).obj ((image (completed l E) c).obj K, L)

/-- The tensor argument at the target, with the recorded completed pullback.
Source: blueprint sk-prop-sf-pf-reduction, final paragraph
(blueprint: lem-fix-compactification-completed-realization). -/
abbrev projectionArgument (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (L : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
  (integralCompletedTensor.{u, u} l E X).obj (K, (integralDerivedPullback.{u, u} l E f).obj L)

/-- The ordinary counit-defined map followed by the canonical target augmentation.
Its unique extension across chi is the completed counit-defined projection; the
reflector's Hom bijection fixes that extension, even for unbounded ordinary tensors.
Source: Stacks 0B56, 099N; node proof steps 8--10
(blueprint: lem-fix-compactification-completed-realization). -/
def augmentedProjection (aX : OpenFactorCoherence.Tensor l E X)
    (aZ : OpenFactorCoherence.Tensor l E c.Z) (aY : OpenFactorCoherence.Tensor l E Y)
    (b : OpenFactorCoherence.Pull l E f)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (L : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
  ((projectionMap (completed l E) c aX.ordinary aZ.ordinary aY.ordinary
    (completedPull_comp l E c.i c.g)).app K).app L ≫
    (image (completed l E) c).map (argumentUnit l E aX b K L)

/-- The actual reduction functor with values in the derived category of strict
completed-module towers. Exact scalar restriction retains every quotient transition.
Source: Stacks 0941; node proof steps 3--4
(blueprint: lem-fix-compactification-completed-realization). -/
abbrev strictReduction (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E W) :=
  S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E W

/-- One derived strict-tower arrow, obtained from the specified counit projection
before any finite evaluation or total inverse limit.
Source: Stacks 0B56, 0941; node proof steps 8--10
(blueprint: lem-fix-compactification-completed-realization). -/
def strictProjection (S : CoefficientDerivedSystemCalculus l E Y)
    (aX : OpenFactorCoherence.Tensor l E X) (aZ : OpenFactorCoherence.Tensor l E c.Z)
    (aY : OpenFactorCoherence.Tensor l E Y) (b : OpenFactorCoherence.Pull l E f)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (L : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
  (strictReduction l E Y S).map (augmentedProjection l E c aX aZ aY b K L)

/-- The ordinary-to-completed source comparison reduced as one strict-system map.
Source: Stacks 099N, 0941; node proof steps 7--9
(blueprint: lem-fix-compactification-completed-realization). -/
def strictSourceUnit (S : CoefficientDerivedSystemCalculus l E Y)
    (aY : OpenFactorCoherence.Tensor l E Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (L : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
  (strictReduction l E Y S).map ((aY.chi l E).app ((image (completed l E) c).obj K, L))

/-- Tensor and pullback coordinates for a specified finite exponent. The compositor
is the adjoint-conjugate geometric compositor, fixed by the same quotient projections.
Source: Stacks 07A4, 0D6D; node proof steps 6--10
(blueprint: lem-fix-compactification-completed-realization). -/
structure FiniteCoordinates (n : ℕ) where
  tensorX : ProEtaleTensorModel X ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
  tensorZ : ProEtaleTensorModel c.Z ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring c.Z)
  tensorY : ProEtaleTensorModel Y ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
  composition : (finite l E (n + 1) (Nat.le_add_left 1 n)).pull (c.i ≫ c.g) =
    proEtaleRingCompositeCoefficients c.i c.g
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring c.Z)
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull c.g)
      ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull c.i)

/-- Equality with the finite counit-defined projection, in the canonical scalar
coordinates. The final arrow is reduction of the actual completed-argument unit.
This equation identifies specified maps, not merely source and target objects.
Source: Stacks 0B56 and 07A6; node proof steps 8--10
(blueprint: lem-fix-compactification-completed-realization). -/
def FiniteProjectionEquation (n : ℕ) (d : FiniteCoordinates l E c n)
    (aX : OpenFactorCoherence.Tensor l E X) (aZ : OpenFactorCoherence.Tensor l E c.Z)
    (aY : OpenFactorCoherence.Tensor l E Y) (b : OpenFactorCoherence.Pull l E f)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (L : DerivedCategory (scalarReductionSource.{u, u} l E Y)) : Prop :=
  let a := reduction l E (n + 1) (Nat.le_add_left 1 n)
  let CX := pbcDerivedExtend (a.map X)
  let CY := pbcDerivedExtend (a.map Y)
  let P := image (completed l E) c
  let Pn := image (finite l E (n + 1) (Nat.le_add_left 1 n)) c
  let Q := aX.ordinary.tensor.obj (K, (pull (completed l E) f).obj L)
  let π := projectionMap (completed l E) c aX.ordinary aZ.ordinary aY.ordinary
    (completedPull_comp l E c.i c.g)
  let πn := projectionMap (finite l E (n + 1) (Nat.le_add_left 1 n)) c
    d.tensorX d.tensorZ d.tensorY d.composition
  let target := (scalarTensor (a.map X) aX.ordinary d.tensorX).app
    (K, (pull (completed l E) f).obj L) ≪≫
      d.tensorX.tensor.mapIso (Iso.prod (Iso.refl _) ((scalarPull a f).app L))
  CY.map ((π.app K).app L) ≫ (comparison a c).app Q ≫
      Pn.map (CX.map (argumentUnit l E aX b K L)) =
    (scalarTensor (a.map Y) aY.ordinary d.tensorY).hom.app (P.obj K, L) ≫
      d.tensorY.tensor.map (Prod.mkHom ((comparison a c).app K) (𝟙 _)) ≫
      (πn.app (CX.obj K)).app (CY.obj L) ≫
      Pn.map (target.inv ≫ CX.map (argumentUnit l E aX b K L))

variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The strict tower already selected in the definition of integral compact support.
This is an alias of that selection, not a new existence choice.
Source: Bhatt--Scholze 6.7.6; compact-support reduction tower, proof step 4
(blueprint: lem-fix-compactification-completed-realization). -/
abbrev supportTower :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (exists_compactSupportReductionTower l E k X Y f hl c))).2.2

/-- The recorded evaluation coordinates of the prescribed strict support tower.
Source: Bhatt--Scholze 6.7.6; reduction-tower construction
(blueprint: lem-fix-compactification-completed-realization). -/
abbrev supportEvaluation :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (exists_compactSupportReductionTower l E k X Y f hl c))).2.2).2).2

/-- Reduction evaluated after exact restriction uses the recorded scalar coordinates.
Source: Stacks 0941, 07A6; node proof step 6
(blueprint: lem-fix-compactification-completed-realization). -/
def strictEvaluation (S : CoefficientDerivedSystemCalculus l E Y) (n : ℕ) :
    strictReduction l E Y S ⋙ coefficientConstantTowerEvaluation l E Y n ≅
      scalarReductionDerivedExtension l E Y n ⋙ scalarReductionDerivedRestriction l E Y n :=
  Functor.isoWhiskerLeft S.reduction (coefficientRestrictedEvaluationIso l E Y n) ≪≫
    Functor.isoWhiskerRight (S.reductionEvaluation n) (coefficientFiniteDerivedRestriction l E Y n)

/-- Completed proper/open realization, with its whole strict-diagram normalization
and the completed counit projection identity, without a Tor-amplitude hypothesis.
Source: blueprint sk-prop-sf-pf-reduction, paragraph 2 and final paragraph;
Stacks 0A07, 0941, 0943, 0B56, 099I, 07A6
(blueprint: lem-fix-compactification-completed-realization).

Proof: (1) The coefficient DVR is Noetherian with finite perfect standard quotients;
finite-type schemes over k are Noetherian. (2) Strict open reduction preserves the
uniform cohomological interval and completeness, giving constructibility of j!K.
(3) Ordinary proper image commutes with the total derived limit of its strict
reduction tower; its augmentation is proper image of the completion unit.
(4) Apply proper image to the strict open comparison. Its quotient transitions
are exactly compactSupportRestrictedTransition; this constructs beta before limit.
(5) Integral direct-image constructibility gives constructibility of the image.
(6) The reduction/limit adjunction identifies each projection with proper perfect
projection followed by the normalized open tensor comparison, in that order.
(7) Constant-to-completed coefficient equivalence and strict tensor/pullback
substitution identify the completed operations with their common quotient towers.
(8) Coefficient restriction preserves the ordinary counit. The reflector Hom
bijection identifies its unique extension across chi with the completed counit.
(9) Completed projection coherence gives the total-limit equality of the actual
finite counit maps, with quotient transitions; no faithfulness of evaluations is
used. (10) The strict open tensor normalization has identity open restriction;
full faithfulness of extension by zero identifies it with the open factor of the
completed projection. Compose the proper identity and this open identity, then
conjugate by the reconstructed canonical realization. -/
theorem completedRealization [QuasiCompact c.i] :
    ∃ (aX : OpenFactorCoherence.Tensor l E X)
      (aZ : OpenFactorCoherence.Tensor l E c.Z) (aY : OpenFactorCoherence.Tensor l E Y)
      (b : OpenFactorCoherence.Pull l E f) (S : CoefficientDerivedSystemCalculus l E Y)
      (d : ∀ n : ℕ, FiniteCoordinates l E c n),
    Nonempty (CoefficientDerivedSystemCoherence l E Y S) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E c.Z
        ((openExtension (completed l E) c.i).mapDerivedCategory.obj K.obj) ∧
      sfIntegralConstructible l E Y ((image (completed l E) c).obj K.obj)) ∧
    ∃ (β : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⋙
          strictReduction l E Y S ≅
        (sfIntegralConstructible l E X).ι ⋙ supportTower l E c k hl)
      (γ : sfCompactSupportFiniteIntegralFunctor l k hl c E ⋙
          (sfIntegralConstructible l E Y).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ supportTower l E c k hl ⋙
          coefficientConstantTowerLimit l E Y),
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      γ.hom.app K ≫ (coefficientConstantTowerProjection l E Y n).app
          ((supportTower l E c k hl).obj K.obj) ≫
          (supportEvaluation l E c k hl n).hom.app K.obj =
        (coefficientFiniteAdjunction l E Y n).unit.app
            ((sfCompactSupportFiniteIntegralFunctor l k hl c E).obj K).obj ≫
          (scalarReductionDerivedRestriction l E Y n).map
            (sfCompactSupportFiniteReductionIso l k hl c E K n).hom) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (m n : ℕ) (h : n ≤ m),
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
          m n h).app ((supportTower l E c k hl).obj K.obj) ≫
          (supportEvaluation l E c k hl n).hom.app K.obj =
        (supportEvaluation l E c k hl m).hom.app K.obj ≫
          compactSupportRestrictedTransition l E c m n h K.obj) ∧
    SfQcqsCompactSupportRealizationSpec l E k hl c
      (sfQcqsCompactSupportRealization l E k hl c) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      (sfQcqsCompactSupportRealization l E k hl c).hom.app K =
        S.adjunction.unit.app ((image (completed l E) c).obj K.obj) ≫
          (coefficientConstantTowerLimit l E Y).map (β.hom.app K) ≫ γ.inv.app K) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (coefficientConstantTowerEvaluation l E Y n).map (β.hom.app K) ≫
          (supportEvaluation l E c k hl n).hom.app K.obj =
        (strictEvaluation l E S n).hom.app ((image (completed l E) c).obj K.obj) ≫
          (scalarReductionDerivedRestriction l E Y n).map
            ((scalarReductionDerivedExtension l E Y n).map
                ((sfQcqsCompactSupportRealization l E k hl c).hom.app K) ≫
              (sfCompactSupportFiniteReductionIso l k hl c E K n).hom)) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (scalarReductionDerivedExtension l E Y n).map
          ((sfQcqsCompactSupportRealization l E k hl c).hom.app K) ≫
          (sfCompactSupportFiniteReductionIso l k hl c E K n).hom =
        (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K.obj) ≫
          orderedReduction l E c n K.obj ≫
          (finiteImageIso l E n c).hom.app
            ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K.obj) ≫
          (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1))
            c).map ((finiteReductionIso l E X n).hom.app K.obj)) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X)
      (L : sfIntegralConstructibleCategory l E Y)
      (hQ : sfIntegralConstructible l E X (projectionArgument l E K.obj L.obj))
      (_hV : sfIntegralConstructible l E Y (projectionSource l E c K.obj L.obj)),
      let Q : sfIntegralConstructibleCategory l E X := ⟨_, hQ⟩
      ∃ π : projectionSource l E c K.obj L.obj ⟶
          (image (completed l E) c).obj Q.obj,
        ((aY.chi l E).app ((image (completed l E) c).obj K.obj, L.obj) ≫ π =
          augmentedProjection l E c aX aZ aY b K.obj L.obj) ∧
        (∀ π' : projectionSource l E c K.obj L.obj ⟶ (image (completed l E) c).obj Q.obj,
          (aY.chi l E).app ((image (completed l E) c).obj K.obj, L.obj) ≫ π' =
            augmentedProjection l E c aX aZ aY b K.obj L.obj → π' = π) ∧
        (∀ n : ℕ, FiniteProjectionEquation l E c n (d n) aX aZ aY b K.obj L.obj) ∧
        (IsIso (strictSourceUnit l E c S aY K.obj L.obj)) ∧
        (∀ (h : IsIso (strictSourceUnit l E c S aY K.obj L.obj)),
          letI := h
          (strictReduction l E Y S).map π =
            inv (strictSourceUnit l E c S aY K.obj L.obj) ≫
              strictProjection l E c S aX aZ aY b K.obj L.obj) ∧
        (∀ (h : IsIso (strictSourceUnit l E c S aY K.obj L.obj)),
          letI := h
          let dc := sfQcqsCompactSupportRealization l E k hl c
          let ρ := (integralCompletedTensor.{u, u} l E Y).map
              (Prod.mkHom (dc.inv.app K) (𝟙 L.obj)) ≫
            S.adjunction.unit.app (projectionSource l E c K.obj L.obj) ≫
              (coefficientConstantTowerLimit l E Y).map
                (inv (strictSourceUnit l E c S aY K.obj L.obj) ≫
                  strictProjection l E c S aX aZ aY b K.obj L.obj ≫ β.hom.app Q) ≫
              γ.inv.app Q
          π ≫ dc.hom.app Q =
            (integralCompletedTensor.{u, u} l E Y).map
                (Prod.mkHom (dc.hom.app K) (𝟙 L.obj)) ≫ ρ)) := by
  sorry

end WeilConjectures.CompactificationCompletedRealization
