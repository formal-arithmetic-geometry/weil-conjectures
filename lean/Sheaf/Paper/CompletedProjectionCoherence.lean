/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.Paper.ProEtaleConstantReductionTower
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import Sheaf.Paper.ProjectionFormulaTotalization

import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
/-!
# Completion coherence of the projection mate

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 0B56, 0941 and 0A07;
proetale.tex, Tags 099M and 099N
(blueprint: lem-pur-compact-support-completed-projection-coherence).

All sites, strict quotient towers, units, adjunctions and coefficient comparisons
are the existing AdicSites constructions. The additional records only present
their canonical tensor comparisons. The ordinary tensor presentation is an input,
as in the landed ringed-topos tensor theorems; the completed and finite comparisons
are conclusions, not extra hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open CategoryTheory.ConstantCompletion
namespace CategoryTheory.AdicSites.ProjectionCoherence

variable {Y X : Site.{u}}

/-- Package the standard derived localization with a tensor model.
Source: Stacks 07A6 (blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def corner (T : Site.{u}) (A : Type u) [CommRing A]
    (t : T.derived A × T.derived A ⥤ T.derived A) : RingedTensorCorner.{u, u + 1} where
  site := T.objects
  topology := T.topology
  ring := T.ring A
  derived := HasDerivedCategory.standard _
  tensor := t

set_option genSizeOf false in
set_option genInjectivity false in
/-- Tensor models with the specified geometric and universally derived pullback.
The Hom bijections are the existing ordinary and derived adjunctions. The tensor
comparison is fixed on flat-term K-flat representatives by RingedTensorEdge.
Source: Stacks 07A4, 07A6, 0B56
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
structure TensorData (f : Morphism Y X) (A : Type u) [CommRing A] where
  tensorY : Y.derived A × Y.derived A ⥤ Y.derived A
  tensorX : X.derived A × X.derived A ⥤ X.derived A
  modelY : RingedTensorModel (corner Y A tensorY)
  modelX : RingedTensorModel (corner X A tensorX)
  edge : RingedTensorEdge (corner Y A tensorY) (corner X A tensorX)
  inverse_eq : edge.inverse = f.inverse
  direct_eq : edge.direct = f.direct
  adjunction_eq : HEq edge.adjunction f.adjunction
  inverseRing_eq : edge.inverseRing = f.algebra.rings.obj (Y.ring A)
  algebra_eq : HEq edge.algebraic (f.algebra.algebra (Y.ring A))
  ringMap_eq : HEq edge.ringMap (constantMap f.algebra A)
  pullback_eq : edge.pullback = f.modulePull A
  pushforward_eq : edge.pushforward = f.modulePush A
  moduleAdjunction_eq : HEq edge.moduleAdjunction (f.moduleAdjunction A)
  left_eq : edge.left = f.pull A
  right_eq : edge.right = f.push A
  epsilon_eq : HEq edge.epsilon (f.modulePull A).mapDerivedCategoryFactorsh.hom
  derivedAdjunction_eq : HEq edge.derivedAdjunction (f.adj A)
  comparison : tensorY ⋙ f.pull A ≅ ((f.pull A).prod (f.pull A)) ⋙ tensorX
  comparison_eq : HEq comparison (edge.tensorComparison modelY modelX)

variable {f : Morphism Y X} {A : Type u} [CommRing A]

/-- The ordinary projection is the counit mate, independently of completion.
Source: Stacks 0B56 (blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def TensorData.projection (o : TensorData f A) (H : X.derived A) (K : Y.derived A) :
    o.tensorY.obj ((f.push A).obj H, K) ⟶
      (f.push A).obj (o.tensorX.obj (H, (f.pull A).obj K)) :=
  (f.adj A).homEquiv _ _
    (o.comparison.hom.app ((f.push A).obj H, K) ≫
      o.tensorX.map (Prod.mkHom ((f.adj A).counit.app H) (𝟙 _)))

variable [IsNoetherianRing A] (I : Ideal A)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Completed tensor comparisons are images of the actual completion units. These
normalizations fix the completed monoidal comparison before defining its mate.
Source: Stacks 099N, 099G, 07A6
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
structure CompletedTensor (o : TensorData f A) where
  insertRight : ∀ U W : X.derived A,
    (X.completion A I).obj (o.tensorX.obj (U, W)) ≅
      (X.completion A I).obj (o.tensorX.obj (U, (X.completion A I).obj W))
  insertRight_eq : ∀ U W : X.derived A,
    (insertRight U W).hom = (X.completion A I).map
      (o.tensorX.map (Prod.mkHom (𝟙 U) ((X.unit A I).app W)))
  pullInsert : ∀ M : Y.derived A,
    (X.completion A I).obj ((f.pull A).obj M) ≅
      (X.completion A I).obj ((f.pull A).obj ((Y.completion A I).obj M))
  pullInsert_eq : ∀ M : Y.derived A,
    (pullInsert M).hom = (X.completion A I).map ((f.pull A).map ((Y.unit A I).app M))
  comparison : ∀ M N : Y.derived A,
    (X.completion A I).obj ((f.pull A).obj ((Y.completion A I).obj (o.tensorY.obj (M, N)))) ≅
      (X.completion A I).obj (o.tensorX.obj
        ((X.completion A I).obj ((f.pull A).obj M),
          (X.completion A I).obj ((f.pull A).obj N)))
  comparison_eq : ∀ M N : Y.derived A,
    (pullInsert (o.tensorY.obj (M, N))).hom ≫ (comparison M N).hom =
      (X.completion A I).map (o.comparison.hom.app (M, N) ≫
        o.tensorX.map (Prod.mkHom ((X.unit A I).app ((f.pull A).obj M))
          ((X.unit A I).app ((f.pull A).obj N))))

variable {I}

/-- The actual completed-adjunction mate, using its counit and completed tensor.
Source: Stacks 099N, 0B56
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def CompletedTensor.projection {o : TensorData f A} (b : CompletedTensor I o)
    (H : X.Complete A I) (K : Y.Complete A I) :
    (Y.completion A I).obj (o.tensorY.obj ((f.push A).obj H.obj, K.obj)) ⟶
      (f.push A).obj ((X.completion A I).obj (o.tensorX.obj (H.obj, (f.pull A).obj K.obj))) :=
  ((f.completeAdjunction A I).homEquiv
    ((Y.reflector A I).obj (o.tensorY.obj ((f.push A).obj H.obj, K.obj)))
    ((X.reflector A I).obj (o.tensorX.obj (H.obj, (f.pull A).obj K.obj)))
    (ObjectProperty.homMk
      ((b.comparison ((f.push A).obj H.obj) K.obj).hom ≫
        (X.completion A I).map (o.tensorX.map
          (Prod.mkHom ((f.completeAdjunction A I).counit.app H).hom (𝟙 _))) ≫
        (b.insertRight H.obj ((f.pull A).obj K.obj)).inv))).hom

/-- One strict-diagram arrow, formed before applying evaluation or derived limit.
Source: Stacks 0E48, 0B56
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def TensorData.towerProjection (o : TensorData f A) (H : X.derived A) (K : Y.derived A) :
    (Y.reduction A I).obj (o.tensorY.obj ((f.push A).obj H, K)) ⟶
      (f.towerPush A).obj ((X.reduction A I).obj (o.tensorX.obj (H, (f.pull A).obj K))) :=
  (Y.reduction A I).map (o.projection H K) ≫
    f.towerProjection A I (o.tensorX.obj (H, (f.pull A).obj K))

set_option genSizeOf false in
set_option genInjectivity false in
/-- Canonical scalar-extension tensor balancing. The scalar edge is the identity
geometric morphism with the actual quotient ring map. Its left derived comparison
and adjunction are the already normalized finite-coefficient constructions.
Source: Stacks 06YY, 07A4
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
structure ScalarTensor (T : Site.{u}) (n : ℕ)
    (t : T.derived A × T.derived A ⥤ T.derived A)
    (tn : T.derived (quotientRing A I n) × T.derived (quotientRing A I n) ⥤
      T.derived (quotientRing A I n)) where
  edge : RingedTensorEdge (corner T A t) (corner T (quotientRing A I n) tn)
  inverse_eq : edge.inverse = 𝟭 _
  direct_eq : edge.direct = 𝟭 _
  adjunction_eq : HEq edge.adjunction (Adjunction.id : 𝟭 (Sheaf T.topology (Type u)) ⊣ 𝟭 _)
  inverseRing_eq : edge.inverseRing = T.ring A
  ringUnderlying_eq : HEq edge.algebraic.ringUnderlying
    (Iso.refl ((sheafCompose T.topology (forget CommRingCat.{u})).obj (T.ring A)))
  ringMap_eq : HEq edge.ringMap (quotient T.topology A I n)
  pullback_eq : edge.pullback = change (quotient T.topology A I n)
  pushforward_eq : edge.pushforward = res (quotient T.topology A I n)
  left_eq : edge.left = T.finiteReduction A I n
  right_eq : edge.right = T.finiteRestriction A I n
  moduleAdjunction_eq : HEq edge.moduleAdjunction (T.finiteModuleAdjunction A I n)
  derivedAdjunction_eq : HEq edge.derivedAdjunction (T.finiteAdjunction A I n)
  left_normalization : ∀ P : Cx (T.ring A), P.IsAcyclicTensorKFlat → (∀ k : ℤ, (P.X k).IsFlat) →
    HEq (derivedPullbackComplexComparison edge.pullback edge.left edge.epsilon P)
      ((extendComparison (quotient T.topology A I n)).app P)
  balancing : t ⋙ T.finiteReduction A I n ≅
    ((T.finiteReduction A I n).prod (T.finiteReduction A I n)) ⋙ tn

/-- Normalize scalar tensor balancing on its two existing K-flat tensor models.
Source: Stacks 07A4 (blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def ScalarTensor.Normalized {T : Site.{u}} {n : ℕ}
    {t : T.derived A × T.derived A ⥤ T.derived A}
    {tn : T.derived (quotientRing A I n) × T.derived (quotientRing A I n) ⥤
      T.derived (quotientRing A I n)}
    (s : ScalarTensor (I := I) T n t tn)
    (m : RingedTensorModel (corner T A t))
    (mn : RingedTensorModel (corner T (quotientRing A I n) tn)) : Prop :=
  HEq s.balancing (s.edge.tensorComparison m mn)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Finite quotient tensors use A/I^(n+1), retaining its module structure.
Source: Stacks 07A4, 0B56
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
structure FiniteTensor (o : TensorData f A) (n : ℕ) where
  tensor : TensorData f (quotientRing A I n)
  scalarY : ScalarTensor (I := I) Y n o.tensorY tensor.tensorY
  scalarX : ScalarTensor (I := I) X n o.tensorX tensor.tensorX
  normalizedY : scalarY.Normalized o.modelY tensor.modelY
  normalizedX : scalarX.Normalized o.modelX tensor.modelX

/-- Target balancing includes the canonical finite coefficient/pullback comparison.
Source: Stacks 07A4 (blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def FiniteTensor.targetBalancing {o : TensorData f A} {n : ℕ}
    (s : FiniteTensor (I := I) o n) (H : X.derived A) (K : Y.derived A) :
    (X.finiteReduction A I n).obj (o.tensorX.obj (H, (f.pull A).obj K)) ≅
      s.tensor.tensorX.obj ((X.finiteReduction A I n).obj H,
        (f.pull (quotientRing A I n)).obj ((Y.finiteReduction A I n).obj K)) :=
  s.scalarX.balancing.app (H, (f.pull A).obj K) ≪≫
    s.tensor.tensorX.mapIso (Iso.prod (Iso.refl _) ((f.finitePullIso A I n).app K))

/-- Finite projection after the specified perfect-coefficient source comparison.
Source: Stacks 0B56, 0944
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def FiniteTensor.projection {o : TensorData f A} {n : ℕ}
    (s : FiniteTensor (I := I) o n) (H : X.derived A) (K : Y.derived A) :
    (Y.finiteReduction A I n).obj (o.tensorY.obj ((f.push A).obj H, K)) ⟶
      (f.push (quotientRing A I n)).obj
        ((X.finiteReduction A I n).obj (o.tensorX.obj (H, (f.pull A).obj K))) :=
  s.scalarY.balancing.hom.app ((f.push A).obj H, K) ≫
    s.tensor.tensorY.map (Prod.mkHom (f.finiteProjection A I n H) (𝟙 _)) ≫
    s.tensor.projection ((X.finiteReduction A I n).obj H) ((Y.finiteReduction A I n).obj K) ≫
    (f.push (quotientRing A I n)).map (s.targetBalancing H K).inv

/-- The completion-unit identity for the completed projection mate.
Source: Stacks 099N, 0B56
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def CompletedTensor.UnitEquation {o : TensorData f A} (b : CompletedTensor I o) : Prop :=
  ∀ (H : X.Complete A I) (K : Y.Complete A I),
    (Y.unit A I).app (o.tensorY.obj ((f.push A).obj H.obj, K.obj)) ≫ b.projection H K =
      o.projection H.obj K.obj ≫ (f.push A).map
        ((X.unit A I).app (o.tensorX.obj (H.obj, (f.pull A).obj K.obj)))

/-- Uniqueness among precisely the arrows with the stated unit identity.
Source: Stacks 099N
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def CompletedTensor.Unique {o : TensorData f A} (b : CompletedTensor I o) : Prop :=
  ∀ (H : X.Complete A I) (K : Y.Complete A I)
    (p : (Y.completion A I).obj (o.tensorY.obj ((f.push A).obj H.obj, K.obj)) ⟶
      (f.push A).obj ((X.completion A I).obj (o.tensorX.obj (H.obj, (f.pull A).obj K.obj)))),
    (Y.unit A I).app (o.tensorY.obj ((f.push A).obj H.obj, K.obj)) ≫ p =
      o.projection H.obj K.obj ≫ (f.push A).map
        ((X.unit A I).app (o.tensorX.obj (H.obj, (f.pull A).obj K.obj))) →
    p = b.projection H K

/-- Total derived inverse limit of one strict-diagram projection.
Source: Stacks 0941, 0A07
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def CompletedTensor.LimitEquation {o : TensorData f A} (b : CompletedTensor I o) : Prop :=
  ∀ (H : X.Complete A I) (K : Y.Complete A I),
    b.projection H K = (Y.rlim A).map (o.towerProjection (I := I) H.obj K.obj) ≫
      (f.directLimitIso A).inv.app ((X.reduction A I).obj
        (o.tensorX.obj (H.obj, (f.pull A).obj K.obj)))

/-- The ordinary transpose of every whole-diagram arrow after a constant augmentation.
Taking the diagram arrow to be a counit includes the requested counit compatibility.
Source: Stacks 07A6, 0941, 0A07
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def TransposeCompatibility (f : Morphism Y X) (A : Type u) [CommRing A] : Prop :=
  ∀ (M : Y.derived A) (Z : Y.towerDerived A) (W : X.towerDerived A)
    (b : (f.towerPull A).obj Z ⟶ W) (j : (Y.delta A).obj M ⟶ Z),
    (f.adj A).homEquiv M ((X.rlim A).obj W)
      ((X.deltaAdjunction A).unit.app ((f.pull A).obj M) ≫
        (X.rlim A).map ((f.constantPullIso A).inv.app M ≫ (f.towerPull A).map j ≫ b)) =
    (Y.deltaAdjunction A).unit.app M ≫
      (Y.rlim A).map (j ≫ (f.towerAdjunction A).homEquiv Z W b) ≫
      (f.directLimitIso A).inv.app W

/-- Evaluation is the actual finite quotient-ring projection mate, with its source
coefficient comparison and tensor balancing. No faithfulness of evaluation is asserted.
Source: Stacks 0B56, 0941, 0944
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def TensorData.FiniteEquation (o : TensorData f A)
    (s : ∀ n : ℕ, FiniteTensor (I := I) o n) : Prop :=
  ∀ (n : ℕ) (H : X.derived A) (K : Y.derived A),
    (Y.evaluate A n).map (o.towerProjection (I := I) H K) ≫
      (f.evaluatePushIso A n).hom.app ((X.reduction A I).obj
        (o.tensorX.obj (H, (f.pull A).obj K))) ≫
      (f.push A).map ((X.finiteEvaluationIso A I n).hom.app
        (o.tensorX.obj (H, (f.pull A).obj K))) ≫
      (f.finiteRestrictionPushIso A I n).hom.app ((X.finiteReduction A I n).obj
        (o.tensorX.obj (H, (f.pull A).obj K))) =
    (Y.finiteEvaluationIso A I n).hom.app (o.tensorY.obj ((f.push A).obj H, K)) ≫
      (Y.finiteRestriction A I n).map ((s n).projection H K)

/-- Simultaneous naturality makes the equalities equalities of specified transformations.
Source: Stacks 0B56, 099N
(blueprint: lem-pur-compact-support-completed-projection-coherence). -/
def CompletedTensor.Natural {o : TensorData f A} (b : CompletedTensor I o) : Prop :=
  ∀ (H H' : X.Complete A I) (K K' : Y.Complete A I) (h : H ⟶ H') (k : K ⟶ K'),
    (Y.completion A I).map (o.tensorY.map (Prod.mkHom ((f.push A).map h.hom) k.hom)) ≫
      b.projection H' K' = b.projection H K ≫ (f.push A).map ((X.completion A I).map
        (o.tensorX.map (Prod.mkHom h.hom ((f.pull A).map k.hom))))

/-- Completion coherence for the integral projection mate, including its finite quotient
and counit normalizations. It holds for every specified ordinary tensor presentation `o`
of the derived tensor on the two sites (the canonical K-flat model convention of the
landed ringed-topos tensor theorems). The completed tensor comparisons, which are unique by
their unit equations, and the finite quotient tensor presentations are constructed
existentially; the only mathematical hypotheses are Noetherianness and perfectness of
the positive quotients.

Source: Stacks Project, `sites-cohomology.tex`, Tags 07A6, 0B56, 0941, 0A07;
`proetale.tex`, Tags 099M and 099N; the eleven-step agent auxiliary in the DAG
(blueprint: lem-pur-compact-support-completed-projection-coherence).

Proof plan:
1. Closed tensor adjunction and completeness of RHom show that completion of a
   tensor-factor unit is invertible (lem-sf-ringed-derived-closed-symmetric-monoidal,
   lem-sf-ringed-rhom-derived-complete). The same Hom calculation using preservation
   of completeness by direct image gives pullInsert. Unit precomposition fixes all
   tensor comparisons and transports ordinary coherence (lem-sp-completed-pullback-adjunction).
2. Transpose the completed mate. Its completed counit followed by the completion unit
   is the ordinary counit. Cancel the factor units to obtain UnitEquation. The target
   is complete, so unit precomposition is injective and gives Unique.
3. On the diagram sites (lem-weil-pbc-diagram-site-realization) use the ring sheaf
   B=(A/I^(n+1)) with actual quotient transitions. A single flat-term K-flat model
   gives the strict scalar-extension tower; exact restriction gives the recorded
   quotientPresentation (lem-pc-kflat-resolution,
   lem-weil-tower-category-levelwise-abelian,
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
4. Derive the componentwise adjunctions with their fraction normalizations
   (lem-pc-pre-derived-adjoint-functors-general). Evaluation at the terminal tower
   index is exact and left adjoint to the diagonal, so the diagonal preserves
   K-injectives (lem-weil-pbc-right-adjoint-preserves-kinjective). On diagonal
   K-injectives the pushforward and limit identities hold literally; quotient
   augmentation has limit equal to the specified completion unit
   (prop-pur-kinjective-resolutions-exist, lem-weil-pbc-kinjective-total-derived,
   lem-weil-pbc-ringed-strict-tower-homotopy-limit).
5. Compare the two composite derived adjunctions through the identical ordinary
   composite direct image. Their normalized right-adjoint comparison is f.directLimitIso.
   Transposing an arbitrary whole tower arrow after a constant augmentation gives
   TransposeCompatibility, including the counits
   (lem-weil-ringed-tower-pushforward-limit-comparison,
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition).
6. Coefficient exchange on the B-ringed diagram, after exact restriction, is
   f.towerProjection: both transposes are counit tensor identity. Evaluation is
   the corresponding finite coefficient mate, by the normalized fraction adjunction.
   No assertion that varying-coefficient evaluation preserves K-injectives is needed.
7. Represent each quotient by the assumed bounded finite-projective A-complex.
   Constant sheafification preserves its quasi-isomorphism and finite-free splittings.
   The specified finite-total projection inverse proves each finite coefficient
   exchange invertible; its cone is zero at every index, so the whole strict exchange
   is invertible (def-weil-pbc-projection-formula-arrows,
   lemma-weil-pbc-projection-formula-totalization).
8. Scalar-extension tensor balancing identifies the B-diagram projection after the
   coefficient exchange with FiniteTensor.projection on evaluation, giving FiniteEquation.
9. Apply lem-weil-pbc-ringed-exchange-tensor-coherence on that diagram square.
   It identifies the whole diagram arrow with reduction of the ordinary projection
   followed by coefficient exchange: this is TensorData.towerProjection before any limit.
10. Tensor-unit normalization and naturality for the actual quotient augmentation
    give exchange times augmentation = pushed augmentation. Total limit and the
    normalized direct-image comparison give rho times eta = P(eta).
11. Apply total derived limit to step 9. Step 10 and naturality of eta give precisely
    UnitEquation for the resulting arrow. Unique identifies it with the completed
    mate, proving CompletedTensor.LimitEquation. All constructions and normalized comparisons are
    natural, proving Natural. No faithfulness of reductions is used. -/
theorem completedProjectionCoherence
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (_hperfect : AdicSites.PerfectQuotients A I) (f : Morphism Y X) (o : TensorData f A) :
    ∃ (b : CompletedTensor I o) (s : ∀ n : ℕ, FiniteTensor (I := I) o n),
      (∀ H : X.derived A, IsIso (f.towerProjection A I H)) ∧
      (∀ (n : ℕ) (H : X.derived A), IsIso (f.finiteProjection A I n H)) ∧
      b.UnitEquation ∧ b.Unique ∧ b.LimitEquation ∧ o.FiniteEquation s ∧
      TransposeCompatibility f A ∧ b.Natural := by
  sorry

end CategoryTheory.AdicSites.ProjectionCoherence
