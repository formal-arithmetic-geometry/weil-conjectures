/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.Paper.ProEtaleConstantReductionTower
public import Sheaf.Paper.ProjectionMateExact
import all Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import Sheaf.Paper.CompletedTensorUnitInsertion
import Sheaf.Paper.PerfectQuotientExchangeNormalization
import Sheaf.SecSmoothPurity.CochainCoefficientArrows
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits

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
universe u w
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

section Proofs

-- Avoid repeated elaboration of the large dependent tensor presentations during linting.
set_option linter.unusedTactic false

attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  CochainComplex.IsAcyclicTensorKFlat CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.symmetricCategory Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactorsh Functor.mapDerivedCategoryFactors

attribute [local irreducible] RingedTensorEdge.tensorComparison
  RingedDerivedNative.monoidal SheafOfModules.monoidalCategory
  ConstantCompletion.quotientPresentation ConstantCompletion.strictLimit
  ConstantCompletion.derivedExtension ConstantCompletion.derivedPull

private theorem tensor_projection_naturality
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {R : B ⥤ A}
    (adj : F ⊣ R) (T : A × A ⥤ A) (U : B × B ⥤ B)
    (t : T ⋙ F ⟶ (F.prod F) ⋙ U)
    {E E' : B} {Q Q' : A} (v : E ⟶ E') (z : Q ⟶ Q') :
    T.map (CategoryTheory.Prod.mkHom (R.map v) z) ≫
        adj.homEquiv _ _ (t.app (R.obj E', Q') ≫
          U.map (CategoryTheory.Prod.mkHom (adj.counit.app E') (𝟙 (F.obj Q')))) =
      adj.homEquiv _ _ (t.app (R.obj E, Q) ≫
          U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))) ≫
        R.map (U.map (CategoryTheory.Prod.mkHom v (F.map z))) := by
  apply adj.homEquiv_naturality_left_square
  have hn := t.naturality (CategoryTheory.Prod.mkHom (R.map v) z)
  dsimp at hn
  rw [← Category.assoc, hn, Category.assoc]
  simp only [Category.assoc, ← U.map_comp]
  congr 2
  ext
  · exact adj.counit.naturality v
  · simp

section SquareTransport
variable {B E B' E' : Type*} [Category B] [Category E] [Category B'] [Category E']

private def SquareFormula
    (T : B × B ⥤ B) (U : E × E ⥤ E)
    (V : B' × B' ⥤ B') (W : E' × E' ⥤ E')
    {F : B ⥤ E} {R : E ⥤ B} {Fn : B' ⥤ E'} {Rn : E' ⥤ B'}
    {G : B ⥤ B'} {J : E ⥤ E'}
    (a : F ⊣ R) (an : Fn ⊣ Rn)
    (cF : T ⋙ F ≅ F.prod F ⋙ U) (cG : T ⋙ G ≅ G.prod G ⋙ V)
    (cJ : U ⋙ J ≅ J.prod J ⋙ W) (cN : V ⋙ Fn ≅ Fn.prod Fn ⋙ W)
    (θ : G ⋙ Fn ≅ F ⋙ J) : Prop :=
  ∀ (H : E) (K : B),
    G.map (a.homEquiv _ _ (cF.hom.app (R.obj H, K) ≫
      U.map (Prod.mkHom (a.counit.app H) (𝟙 _)))) ≫
      (mateEquiv a an (TwoSquare.mk _ _ _ _ θ.hom)).natTrans.app
        (U.obj (H, F.obj K)) ≫
      Rn.map (cJ.hom.app (H, F.obj K) ≫
        W.map (Prod.mkHom (𝟙 _) (θ.inv.app K))) =
    cG.hom.app (R.obj H, K) ≫
      V.map (Prod.mkHom
        ((mateEquiv a an (TwoSquare.mk _ _ _ _ θ.hom)).natTrans.app H) (𝟙 _)) ≫
      an.homEquiv _ _ (cN.hom.app (Rn.obj (J.obj H), G.obj K) ≫
        W.map (Prod.mkHom (an.counit.app (J.obj H)) (𝟙 _)))

private theorem square_formula_transport
    (T : B × B ⥤ B) (U : E × E ⥤ E)
    (V : B' × B' ⥤ B') (W : E' × E' ⥤ E')
    {F F₀ : B ⥤ E} {R R₀ : E ⥤ B} {Fn Fn₀ : B' ⥤ E'} {Rn Rn₀ : E' ⥤ B'}
    {G G₀ : B ⥤ B'} {J J₀ : E ⥤ E'}
    (hF : F = F₀) (hR : R = R₀) (hN : Fn = Fn₀) (hRn : Rn = Rn₀)
    (hG : G = G₀) (hJ : J = J₀)
    (a : F ⊣ R) (a₀ : F₀ ⊣ R₀) (ha : HEq a a₀)
    (an : Fn ⊣ Rn) (an₀ : Fn₀ ⊣ Rn₀) (han : HEq an an₀)
    (cF : T ⋙ F ≅ F.prod F ⋙ U) (cF₀ : T ⋙ F₀ ≅ F₀.prod F₀ ⋙ U)
    (hcF : HEq cF cF₀)
    (cG : T ⋙ G ≅ G.prod G ⋙ V) (cG₀ : T ⋙ G₀ ≅ G₀.prod G₀ ⋙ V)
    (hcG : HEq cG cG₀)
    (cJ : U ⋙ J ≅ J.prod J ⋙ W) (cJ₀ : U ⋙ J₀ ≅ J₀.prod J₀ ⋙ W)
    (hcJ : HEq cJ cJ₀)
    (cN : V ⋙ Fn ≅ Fn.prod Fn ⋙ W) (cN₀ : V ⋙ Fn₀ ≅ Fn₀.prod Fn₀ ⋙ W)
    (hcN : HEq cN cN₀)
    (θ : G ⋙ Fn ≅ F ⋙ J) (θ₀ : G₀ ⋙ Fn₀ ≅ F₀ ⋙ J₀) (hθ : HEq θ θ₀)
    (h : SquareFormula T U V W a an cF cG cJ cN θ) :
    SquareFormula T U V W a₀ an₀ cF₀ cG₀ cJ₀ cN₀ θ₀ := by
  subst_vars
  exact h

end SquareTransport

omit [IsNoetherianRing A] in
private theorem finite_projection_edges
    {ty : Y.derived A × Y.derived A ⥤ Y.derived A}
    {tx : X.derived A × X.derived A ⥤ X.derived A} (n : ℕ)
    {tyn : Y.derived (quotientRing A I n) × Y.derived (quotientRing A I n) ⥤
      Y.derived (quotientRing A I n)}
    {txn : X.derived (quotientRing A I n) × X.derived (quotientRing A I n) ⥤
      X.derived (quotientRing A I n)}
    (e : RingedTensorEdge (corner Y A ty) (corner X A tx))
    (ey : RingedTensorEdge (corner Y A ty) (corner Y (quotientRing A I n) tyn))
    (ex : RingedTensorEdge (corner X A tx) (corner X (quotientRing A I n) txn))
    (en : RingedTensorEdge (corner Y (quotientRing A I n) tyn)
      (corner X (quotientRing A I n) txn))
    (my : RingedTensorModel (corner Y A ty)) (mx : RingedTensorModel (corner X A tx))
    (myn : RingedTensorModel (corner Y (quotientRing A I n) tyn))
    (mxn : RingedTensorModel (corner X (quotientRing A I n) txn))
    (hl : e.left = f.pull A) (hr : e.right = f.push A)
    (ha : HEq e.derivedAdjunction (f.adj A))
    (hln : en.left = f.pull (quotientRing A I n))
    (hrn : en.right = f.push (quotientRing A I n))
    (han : HEq en.derivedAdjunction (f.adj (quotientRing A I n)))
    (hly : ey.left = Y.finiteReduction A I n)
    (hlx : ex.left = X.finiteReduction A I n)
    (cmp : ty ⋙ f.pull A ≅ (f.pull A).prod (f.pull A) ⋙ tx)
    (hcmp : HEq cmp (e.tensorComparison my mx))
    (cmpn : tyn ⋙ f.pull (quotientRing A I n) ≅
      (f.pull (quotientRing A I n)).prod (f.pull (quotientRing A I n)) ⋙ txn)
    (hcmpn : HEq cmpn (en.tensorComparison myn mxn))
    (cy : ty ⋙ Y.finiteReduction A I n ≅
      (Y.finiteReduction A I n).prod (Y.finiteReduction A I n) ⋙ tyn)
    (hy : HEq cy (ey.tensorComparison my myn))
    (cx : tx ⋙ X.finiteReduction A I n ≅
      (X.finiteReduction A I n).prod (X.finiteReduction A I n) ⋙ txn)
    (hx : HEq cx (ex.tensorComparison mx mxn))
    (sq : RingedTensorSquare (corner Y A ty) (corner X A tx)
      (corner Y (quotientRing A I n) tyn) (corner X (quotientRing A I n) txn)
      e ey ex en)
    (hθ : HEq sq.derivedComparison (f.finitePullIso A I n).symm)
    (H : X.derived A) (K : Y.derived A) :
    cy.hom.app ((f.push A).obj H, K) ≫
      tyn.map (Prod.mkHom (f.finiteProjection A I n H) (𝟙 _)) ≫
      (f.adj (quotientRing A I n)).homEquiv _ _
        (cmpn.hom.app ((f.push (quotientRing A I n)).obj
          ((X.finiteReduction A I n).obj H), (Y.finiteReduction A I n).obj K) ≫
          txn.map (Prod.mkHom ((f.adj (quotientRing A I n)).counit.app
            ((X.finiteReduction A I n).obj H)) (𝟙 _))) =
    (Y.finiteReduction A I n).map ((f.adj A).homEquiv _ _
      (cmp.hom.app ((f.push A).obj H, K) ≫
        tx.map (Prod.mkHom ((f.adj A).counit.app H) (𝟙 _)))) ≫
      f.finiteProjection A I n (tx.obj (H, (f.pull A).obj K)) ≫
        (f.push (quotientRing A I n)).map
          (cx.hom.app (H, (f.pull A).obj K) ≫
            txn.map (Prod.mkHom (𝟙 _) ((f.finitePullIso A I n).hom.app K))) := by
  have hh : SquareFormula ty tx tyn txn e.derivedAdjunction en.derivedAdjunction
      (e.tensorComparison my mx) (ey.tensorComparison my myn)
      (ex.tensorComparison mx mxn) (en.tensorComparison myn mxn) sq.derivedComparison := by
    intro H K
    exact (ringedExchangeTensorCoherence sq my mx myn mxn).1 H K
  have h := square_formula_transport ty tx tyn txn hl hr hln hrn hly hlx
    e.derivedAdjunction (f.adj A) ha en.derivedAdjunction (f.adj (quotientRing A I n)) han
    (e.tensorComparison my mx) cmp hcmp.symm
    (ey.tensorComparison my myn) cy hy.symm
    (ex.tensorComparison mx mxn) cx hx.symm
    (en.tensorComparison myn mxn) cmpn hcmpn.symm
    sq.derivedComparison (f.finitePullIso A I n).symm hθ hh H K
  have hex (F : X.derived A) :
      (mateEquiv (f.adj A) (f.adj (quotientRing A I n))
        (TwoSquare.mk _ _ _ _ (f.finitePullIso A I n).inv)).natTrans.app F =
        f.finiteProjection A I n F := by
    apply ((f.adj (quotientRing A I n)).homEquiv _ _).symm.injective
    dsimp only [Functor.comp_obj]
    rw [Morphism.finiteProjection, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact mateEquiv_counit (f.adj A) (f.adj (quotientRing A I n))
      (TwoSquare.mk _ _ _ _ (f.finitePullIso A I n).inv) F
  simpa only [SquareFormula, Iso.symm_hom, Iso.symm_inv, hex,
    Functor.comp_obj, Functor.id_obj] using h.symm

omit [IsNoetherianRing A] in
private theorem finite_projection_square (o : TensorData f A) (n : ℕ)
    (s : FiniteTensor (I := I) o n)
    (sq : RingedTensorSquare (corner Y A o.tensorY) (corner X A o.tensorX)
      (corner Y (quotientRing A I n) s.tensor.tensorY)
      (corner X (quotientRing A I n) s.tensor.tensorX)
      o.edge s.scalarY.edge s.scalarX.edge s.tensor.edge)
    (hθ : HEq sq.derivedComparison (f.finitePullIso A I n).symm)
    (H : X.derived A) (K : Y.derived A) :
    s.projection H K = (Y.finiteReduction A I n).map (o.projection H K) ≫
      f.finiteProjection A I n (o.tensorX.obj (H, (f.pull A).obj K)) := by
  apply (cancel_mono ((f.push (quotientRing A I n)).map
    (s.targetBalancing H K).hom)).1
  dsimp only [FiniteTensor.projection]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, Category.comp_id]
  dsimp only [FiniteTensor.targetBalancing, TensorData.projection,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  exact finite_projection_edges n o.edge s.scalarY.edge s.scalarX.edge s.tensor.edge
    o.modelY o.modelX s.tensor.modelY s.tensor.modelX
    o.left_eq o.right_eq o.derivedAdjunction_eq
    s.tensor.left_eq s.tensor.right_eq s.tensor.derivedAdjunction_eq
    s.scalarY.left_eq s.scalarX.left_eq o.comparison o.comparison_eq
    s.tensor.comparison s.tensor.comparison_eq
    s.scalarY.balancing s.normalizedY s.scalarX.balancing s.normalizedX sq hθ H K

section ReflectorHelpers
variable {B E : Type*} [Category B] [Category E]

private theorem iso_of_complete_precomp
    (P : ObjectProperty B) {X Y : B} (f : X ⟶ Y) (hX : P X) (hY : P Y)
    (h : ∀ Z : B, P Z → Function.Bijective (fun g : Y ⟶ Z ↦ f ≫ g)) : IsIso f := by
  obtain ⟨g, hg⟩ := (h X hX).2 (𝟙 X)
  refine ⟨⟨g, hg, ?_⟩⟩
  apply (h Y hY).1
  simp only [← Category.assoc, hg, Category.id_comp, Category.comp_id]

private theorem reflector_map_iso
    (P : ObjectProperty B) (T : B ⥤ B) (η : 𝟭 B ⟶ T)
    (hT : ∀ X, P (T.obj X))
    (hη : ∀ (X Z : B), P Z →
      Function.Bijective (fun g : T.obj X ⟶ Z ↦ η.app X ≫ g))
    {X Y : B} (f : X ⟶ Y)
    (hf : ∀ Z : B, P Z → Function.Bijective (fun g : Y ⟶ Z ↦ f ≫ g)) :
    IsIso (T.map f) := by
  apply iso_of_complete_precomp P _ (hT X) (hT Y)
  intro Z hZ
  let ex := Equiv.ofBijective _ (hη X Z hZ)
  let ey := Equiv.ofBijective _ (hη Y Z hZ)
  let ef := Equiv.ofBijective _ (hf Z hZ)
  convert (ey.trans ef |>.trans ex.symm).bijective using 1
  funext g
  apply ex.injective
  change η.app X ≫ T.map f ≫ g = ex ((ey.trans ef |>.trans ex.symm) g)
  change η.app X ≫ T.map f ≫ g = ex (ex.symm (ef (ey g)))
  rw [ex.apply_symm_apply]
  exact (η.naturality_assoc f g).symm

private theorem reflector_pullback_unit_iso
    (P : ObjectProperty B) (P' : ObjectProperty E)
    (T : B ⥤ B) (T' : E ⥤ E) (η : 𝟭 B ⟶ T) (η' : 𝟭 E ⟶ T')
    (hT' : ∀ X, P' (T'.obj X))
    (hη : ∀ (X Z : B), P Z →
      Function.Bijective (fun g : T.obj X ⟶ Z ↦ η.app X ≫ g))
    (hη' : ∀ (X Z : E), P' Z →
      Function.Bijective (fun g : T'.obj X ⟶ Z ↦ η'.app X ≫ g))
    (L : B ⥤ E) (R : E ⥤ B) (a : L ⊣ R)
    (hR : ∀ Z, P' Z → P (R.obj Z)) (X : B) :
    IsIso (T'.map (L.map (η.app X))) := by
  apply reflector_map_iso P' T' η' hT' hη'
  intro Z hZ
  let ex := a.homEquiv X Z
  let ey := a.homEquiv (T.obj X) Z
  let eη := Equiv.ofBijective _ (hη X (R.obj Z) (hR Z hZ))
  convert (ey.trans eη |>.trans ex.symm).bijective using 1 <;> try rfl
  funext g
  apply ex.injective
  change ex (L.map (η.app X) ≫ g) = ex (ex.symm (eη (ey g)))
  rw [ex.apply_symm_apply]
  exact a.homEquiv_naturality_left (η.app X) g

end ReflectorHelpers

private theorem lift_model_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (q : C ⥤ D) (F G : D ⥤ E)
    (ff : ((Functor.whiskeringLeft C D E).obj q).FullyFaithful)
    (e : q ⋙ F ≅ q ⋙ G) : Nonempty (F ≅ G) :=
  ⟨ff.preimageIso e⟩

private def native_tensor_model (T : Site.{u}) (A : Type u) [CommRing A] :
    RingedTensorModel (corner T A (constantDerivedTensor T.topology A)) := by
  let F := corner T A (constantDerivedTensor T.topology A)
  let ι : F.mateFlat.FullSubcategory ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients
        (R := T.ring A) : ObjectProperty (Cx (T.ring A))) := {
    obj := fun P ↦ ⟨P.obj,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
    map := fun a ↦ ObjectProperty.homMk a.hom }
  exact ⟨Functor.isoWhiskerLeft (ι.prod ι)
    (RingedDerivedNative.comparison.{u, u, u, u + 1} T.topology (T.ring A))⟩

attribute [local irreducible] native_tensor_model

private theorem tensor_native_iso (T : Site.{u}) (A : Type u) [CommRing A]
    (t : T.derived A × T.derived A ⥤ T.derived A) (m : RingedTensorModel (corner T A t)) :
    Nonempty (t ≅ constantDerivedTensor T.topology A) := by
  let F := corner T A t
  obtain ⟨ff⟩ := SheafOfModules.mateResolvingFF F (T.derived A)
  exact lift_model_iso _ _ _ ff
    (m.representative.symm ≪≫ (native_tensor_model T A).representative)

private theorem tensor_unit_insertions (T : Site.{u}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    (t : T.derived A × T.derived A ⥤ T.derived A) (m : RingedTensorModel (corner T A t)) :
    (∀ U W : T.derived A, IsIso ((T.completion A I).map
      (t.map (Prod.mkHom ((T.unit A I).app U) (𝟙 W))))) ∧
    (∀ U W : T.derived A, IsIso ((T.completion A I).map
      (t.map (Prod.mkHom (𝟙 U) ((T.unit A I).app W))))) := by
  obtain ⟨_, _, _, _, h⟩ := completedTensorUnitInsertion T.topology T.topology A I
    (𝟭 _) (𝟭 _) Adjunction.id
  obtain ⟨_, _, _, _, hl, hr, _⟩ := h
  obtain ⟨e⟩ := tensor_native_iso T A t m
  constructor
  · intro U W
    have hi : IsIso ((T.completion A I).map ((constantDerivedTensor T.topology A).map
        (Prod.mkHom ((T.unit A I).app U) (𝟙 W)))) := hl U W
    have hn := congrArg ((T.completion A I).map)
      (e.hom.naturality (Prod.mkHom ((T.unit A I).app U) (𝟙 W)))
    rw [Functor.map_comp, Functor.map_comp] at hn
    have : IsIso ((T.completion A I).map (t.map
        (Prod.mkHom ((T.unit A I).app U) (𝟙 W))) ≫
        (T.completion A I).map (e.hom.app ((T.completion A I).obj U, W))) := by
      rw [hn]
      exact inferInstance
    exact IsIso.of_isIso_comp_right _ ((T.completion A I).map (e.hom.app _))
  · intro U W
    have hi : IsIso ((T.completion A I).map ((constantDerivedTensor T.topology A).map
        (Prod.mkHom (𝟙 U) ((T.unit A I).app W)))) := hr U W
    have hn := congrArg ((T.completion A I).map)
      (e.hom.naturality (Prod.mkHom (𝟙 U) ((T.unit A I).app W)))
    rw [Functor.map_comp, Functor.map_comp] at hn
    have : IsIso ((T.completion A I).map (t.map
        (Prod.mkHom (𝟙 U) ((T.unit A I).app W))) ≫
        (T.completion A I).map (e.hom.app (U, (T.completion A I).obj W))) := by
      rw [hn]
      exact inferInstance
    exact IsIso.of_isIso_comp_right _ ((T.completion A I).map (e.hom.app _))

private theorem completed_tensor_exists (o : TensorData f A) : Nonempty (CompletedTensor I o) := by
  have hp (M : Y.derived A) :
      IsIso ((X.completion A I).map ((f.pull A).map ((Y.unit A I).app M))) :=
    reflector_pullback_unit_iso (Y.IsComplete A I) (X.IsComplete A I)
      (Y.completion A I) (X.completion A I) (Y.unit A I) (X.unit A I)
      (X.completion_properties A I).1 (Y.completion_properties A I).2.1
      (X.completion_properties A I).2.1 (f.pull A) (f.push A) (f.adj A)
      (f.push_complete A I) M
  obtain ⟨hl, hr⟩ := tensor_unit_insertions X A I o.tensorX o.modelX
  have ht (U W : X.derived A) : IsIso ((X.completion A I).map
      (o.tensorX.map (Prod.mkHom ((X.unit A I).app U) ((X.unit A I).app W)))) := by
    have h₁ := hl U W
    have h₂ := hr ((X.completion A I).obj U) W
    have he : Prod.mkHom ((X.unit A I).app U) ((X.unit A I).app W) =
        Prod.mkHom ((X.unit A I).app U) (𝟙 W) ≫
          Prod.mkHom (𝟙 _) ((X.unit A I).app W) := by ext <;> simp
    rw [he, o.tensorX.map_comp, (X.completion A I).map_comp]
    infer_instance
  let pi (M : Y.derived A) := asIso
    ((X.completion A I).map ((f.pull A).map ((Y.unit A I).app M)))
  let co (M N : Y.derived A) :=
    (pi (o.tensorY.obj (M, N))).symm ≪≫
      (X.completion A I).mapIso (o.comparison.app (M, N)) ≪≫
        asIso ((X.completion A I).map (o.tensorX.map
          (Prod.mkHom ((X.unit A I).app ((f.pull A).obj M))
            ((X.unit A I).app ((f.pull A).obj N)))))
  refine ⟨{
    insertRight := fun U W ↦ asIso ((X.completion A I).map
      (o.tensorX.map (Prod.mkHom (𝟙 U) ((X.unit A I).app W))))
    insertRight_eq := fun _ _ ↦ rfl
    pullInsert := pi
    pullInsert_eq := fun _ ↦ rfl
    comparison := co
    comparison_eq := ?_ }⟩
  intro M N
  dsimp only [co, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    ← (X.completion A I).map_comp]
  rfl

private theorem completed_unique {o : TensorData f A} (b : CompletedTensor I o)
    (hb : b.UnitEquation) : b.Unique := by
  intro H K p hp
  apply ((Y.completion_properties A I).2.1 _ _
    (f.push_complete A I _ ((X.completion_properties A I).1 _))).injective
  exact hp.trans (hb H K).symm

private theorem completed_counit_unit (H : X.Complete A I) :
    (X.unit A I).app ((f.pull A).obj ((f.push A).obj H.obj)) ≫
        ((f.completeAdjunction A I).counit.app H).hom = (f.adj A).counit.app H.obj := by
  apply ((f.adj A).homEquiv _ _).injective
  have h := (f.completeAdjunction_existsUnique A I).exists.choose_spec
    ((f.completePush A I).obj H) H ((f.completeAdjunction A I).counit.app H)
  change ((f.completeAdjunction A I).homEquiv _ _
    ((f.completeAdjunction A I).counit.app H)).hom = _ at h
  have hc : (f.completeAdjunction A I).homEquiv _ H
      ((f.completeAdjunction A I).counit.app H) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact (f.completeAdjunction A I).right_triangle_components H
  calc
    _ = (((f.completeAdjunction A I).homEquiv _ H
        ((f.completeAdjunction A I).counit.app H))).hom := h.symm
    _ = 𝟙 ((f.push A).obj H.obj) :=
      congrArg (fun z : (f.completePush A I).obj H ⟶ (f.completePush A I).obj H ↦ z.hom) hc
    _ = (f.adj A).homEquiv _ H.obj ((f.adj A).counit.app H.obj) := by
      symm
      rw [Adjunction.homEquiv_unit]
      exact (f.adj A).right_triangle_components H.obj

private theorem completed_unit_equation {o : TensorData f A} (b : CompletedTensor I o) :
    b.UnitEquation := by
  intro H K
  let M := o.tensorY.obj ((f.push A).obj H.obj, K.obj)
  let N := o.tensorX.obj (H.obj, (f.pull A).obj K.obj)
  let c := (b.comparison ((f.push A).obj H.obj) K.obj).hom ≫
    (X.completion A I).map (o.tensorX.map
      (Prod.mkHom ((f.completeAdjunction A I).counit.app H).hom (𝟙 _))) ≫
    (b.insertRight H.obj ((f.pull A).obj K.obj)).inv
  have hp : b.projection H K = (f.adj A).homEquiv _ _
      ((X.unit A I).app ((f.pull A).obj ((Y.completion A I).obj M)) ≫ c) := by
    exact (f.completeAdjunction_existsUnique A I).exists.choose_spec
      ((Y.reflector A I).obj M) ((X.reflector A I).obj N) (ObjectProperty.homMk c)
  rw [hp, ← (f.adj A).homEquiv_naturality_left]
  rw [TensorData.projection, ← (f.adj A).homEquiv_naturality_right]
  apply congrArg ((f.adj A).homEquiv M ((X.completion A I).obj N))
  change (f.pull A).map ((Y.unit A I).app M) ≫ _ ≫ c =
    (o.comparison.hom.app ((f.push A).obj H.obj, K.obj) ≫
      o.tensorX.map (Prod.mkHom ((f.adj A).counit.app H.obj) (𝟙 _))) ≫
        (X.unit A I).app N
  have hu : (f.pull A).map ((Y.unit A I).app M) ≫
      (X.unit A I).app ((f.pull A).obj ((Y.completion A I).obj M)) =
    (X.unit A I).app ((f.pull A).obj M) ≫
      (X.completion A I).map ((f.pull A).map ((Y.unit A I).app M)) := by
    exact (X.unit A I).naturality ((f.pull A).map ((Y.unit A I).app M))
  rw [← Category.assoc, hu, Category.assoc]
  dsimp only [c]
  rw [← b.pullInsert_eq]
  simp only [Category.assoc]
  rw [← Category.assoc (b.pullInsert M).hom, b.comparison_eq]
  rw [← (X.completion A I).map_comp_assoc, Category.assoc]
  rw [← o.tensorX.map_comp]
  have hc := completed_counit_unit (f := f) (I := I) H
  have he : Prod.mkHom ((X.unit A I).app ((f.pull A).obj ((f.push A).obj H.obj)))
      ((X.unit A I).app ((f.pull A).obj K.obj)) ≫
      Prod.mkHom ((f.completeAdjunction A I).counit.app H).hom (𝟙 _) =
    Prod.mkHom ((f.adj A).counit.app H.obj) ((X.unit A I).app ((f.pull A).obj K.obj)) := by
    apply Prod.ext
    · exact hc
    · simp
  rw [he]
  rw [← (X.unit A I).naturality_assoc]
  have ht : o.tensorX.map
      (Prod.mkHom ((f.adj A).counit.app H.obj) ((X.unit A I).app ((f.pull A).obj K.obj))) =
    o.tensorX.map (Prod.mkHom ((f.adj A).counit.app H.obj) (𝟙 _)) ≫
      o.tensorX.map (Prod.mkHom (𝟙 H.obj) ((X.unit A I).app ((f.pull A).obj K.obj))) := by
    rw [← o.tensorX.map_comp]
    congr 1
    ext <;> simp
  rw [ht]
  dsimp only [Functor.id_map]
  simp only [Category.assoc]
  have hi := (X.unit A I).naturality
    (o.tensorX.map (Prod.mkHom (𝟙 H.obj) ((X.unit A I).app ((f.pull A).obj K.obj))))
  dsimp only [Functor.id_map] at hi
  erw [reassoc_of% hi]
  rw [← b.insertRight_eq]
  simp only [Iso.hom_inv_id, Category.comp_id]
  rfl

private theorem conjugate_transpose
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e : L₂ ≅ L₁) (M : C) (W : D) (k : L₂.obj M ⟶ W) :
    a₁.homEquiv M W (e.inv.app M ≫ k) =
      a₂.homEquiv M W k ≫ (conjugateIsoEquiv a₁ a₂ e).inv.app W := by
  let t := conjugateEquiv a₂ a₁ e.inv
  change a₁.homEquiv M W (e.inv.app M ≫ k) = a₂.homEquiv M W k ≫ t.app W
  rw [a₁.homEquiv_unit, a₂.homEquiv_unit, R₁.map_comp]
  rw [Category.assoc, t.naturality, ← Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun q ↦ q ≫ R₁.map k) (unit_conjugateEquiv a₂ a₁ e.inv M).symm

private theorem transpose_compatibility (f : Morphism Y X) (A : Type u) [CommRing A] :
    TransposeCompatibility f A := by
  intro M Z W b j
  have h := conjugate_transpose ((f.adj A).comp (X.deltaAdjunction A))
    ((Y.deltaAdjunction A).comp (f.towerAdjunction A)) (f.constantPullIso A)
    M W ((f.towerPull A).map j ≫ b)
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv] at h
  change (f.adj A).homEquiv M ((X.rlim A).obj W)
      ((X.deltaAdjunction A).homEquiv ((f.pull A).obj M) W
        ((f.constantPullIso A).inv.app M ≫ (f.towerPull A).map j ≫ b)) =
    (Y.deltaAdjunction A).homEquiv M ((f.towerPush A).obj W)
      ((f.towerAdjunction A).homEquiv ((Y.delta A).obj M) W
        ((f.towerPull A).map j ≫ b)) ≫ (f.directLimitIso A).inv.app W at h
  rw [(f.towerAdjunction A).homEquiv_naturality_left] at h
  simpa only [(X.deltaAdjunction A).homEquiv_unit,
    (Y.deltaAdjunction A).homEquiv_unit, Category.assoc] using h

omit [IsNoetherianRing A] in
private theorem ordinary_projection_natural (o : TensorData f A)
    {H H' : X.derived A} {K K' : Y.derived A} (h : H ⟶ H') (k : K ⟶ K') :
    o.tensorY.map (Prod.mkHom ((f.push A).map h) k) ≫ o.projection H' K' =
      o.projection H K ≫ (f.push A).map
        (o.tensorX.map (Prod.mkHom h ((f.pull A).map k))) :=
  tensor_projection_naturality (f.adj A) o.tensorY o.tensorX o.comparison.hom h k

private theorem completed_natural {o : TensorData f A} (b : CompletedTensor I o)
    (hb : b.UnitEquation) : b.Natural := by
  intro H H' K K' h k
  apply ((Y.completion_properties A I).2.1 _ _
    (f.push_complete A I _ ((X.completion_properties A I).1 _))).injective
  change (Y.unit A I).app _ ≫ _ = (Y.unit A I).app _ ≫ _
  have hu := (Y.unit A I).naturality
    (o.tensorY.map (Prod.mkHom ((f.push A).map h.hom) k.hom))
  dsimp only [Functor.id_map] at hu
  rw [← Category.assoc, ← hu, Category.assoc, hb H' K',
    ← Category.assoc, ordinary_projection_natural, Category.assoc]
  rw [← Category.assoc ((Y.unit A I).app _), hb H K, Category.assoc,
    ← (f.push A).map_comp, ← (f.push A).map_comp]
  congr 1
  exact congrArg (f.push A).map ((X.unit A I).naturality
    (o.tensorX.map (Prod.mkHom h.hom ((f.pull A).map k.hom))))

omit [IsNoetherianRing A] in
private theorem tower_mate_eq (F : X.derived A) :
    (mateEquiv (f.adj A) (f.towerAdjunction A)
      (TwoSquare.mk _ _ _ _ (f.reductionPullIso A I).hom)).natTrans.app F =
      f.towerProjection A I F := by
  apply ((f.towerAdjunction A).homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj]
  rw [Morphism.towerProjection, Equiv.symm_apply_apply,
    Adjunction.homEquiv_counit]
  exact mateEquiv_counit (f.adj A) (f.towerAdjunction A)
    (TwoSquare.mk _ _ _ _ (f.reductionPullIso A I).hom) F

omit [IsNoetherianRing A] in
private theorem strict_exchange_eq (p : PerfectQuotientExchange.Presentation f A I)
    (F : X.derived A) :
    (PerfectQuotientExchange.strictExchange p).app F =
      p.reductionY.tower.hom.app ((f.push A).obj F) ≫
        f.towerProjection A I F ≫
          (f.towerPush A).map (p.reductionX.tower.inv.app F) := by
  simp only [PerfectQuotientExchange.strictExchange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, tower_mate_eq]

omit [IsNoetherianRing A] in
private theorem completion_exchange_eq (p : PerfectQuotientExchange.Presentation f A I)
    (F : X.derived A) :
    PerfectQuotientExchange.completionExchange p F =
      (Y.rlim A).map (f.towerProjection A I F) ≫
        (f.directLimitIso A).inv.app ((X.reduction A I).obj F) := by
  have hn := (f.directLimitIso A).inv.naturality (p.reductionX.tower.hom.app F)
  dsimp only [Functor.comp_map] at hn
  change (Y.rlim A).map (p.reductionY.tower.inv.app ((f.push A).obj F)) ≫
    (Y.rlim A).map ((PerfectQuotientExchange.strictExchange p).app F) ≫
      (f.directLimitIso A).inv.app _ ≫
        (f.push A).map ((X.rlim A).map (p.reductionX.tower.hom.app F)) = _
  rw [strict_exchange_eq]
  simp only [Functor.map_comp, Category.assoc]
  erw [← hn]
  have hy : (Y.rlim A).map (p.reductionY.tower.inv.app ((f.push A).obj F)) ≫
      (Y.rlim A).map (p.reductionY.tower.hom.app ((f.push A).obj F)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  have hx : (Y.rlim A).map ((f.towerPush A).map (p.reductionX.tower.inv.app F)) ≫
      (Y.rlim A).map ((f.towerPush A).map (p.reductionX.tower.hom.app F)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Functor.map_id]
  simp only [← Category.assoc]
  erw [hy]
  simp only [Category.id_comp, Category.assoc]
  rw [reassoc_of% hx]

private theorem completed_limit {o : TensorData f A} (b : CompletedTensor I o)
    (hb : b.Unique)
    (hρ : ∀ F : X.derived A,
      (Y.unit A I).app ((f.push A).obj F) ≫
        (Y.rlim A).map (f.towerProjection A I F) ≫
          (f.directLimitIso A).inv.app ((X.reduction A I).obj F) =
            (f.push A).map ((X.unit A I).app F)) : b.LimitEquation := by
  intro H K
  symm
  apply hb H K
  dsimp only [TensorData.towerProjection]
  rw [Functor.map_comp]
  have hn := (Y.unit A I).naturality (o.projection H.obj K.obj)
  change o.projection H.obj K.obj ≫ (Y.unit A I).app _ =
    (Y.unit A I).app _ ≫ (Y.rlim A).map ((Y.reduction A I).map _) at hn
  rw [← Category.assoc, ← Category.assoc, ← hn, Category.assoc, Category.assoc, hρ]

private theorem perfect_exchange_properties (hperfect : PerfectQuotients A I) :
    (∀ F : X.derived A, IsIso (f.towerProjection A I F)) ∧
    (∀ (n : ℕ) (F : X.derived A), IsIso (f.finiteProjection A I n F)) ∧
    (∀ F : X.derived A,
      (Y.unit A I).app ((f.push A).obj F) ≫
        (Y.rlim A).map (f.towerProjection A I F) ≫
          (f.directLimitIso A).inv.app ((X.reduction A I).obj F) =
            (f.push A).map ((X.unit A I).app F)) ∧
    (∀ (F : X.derived A) (n : ℕ),
      (Y.evaluate A n).map (f.towerProjection A I F) ≫
        (f.evaluatePushIso A n).hom.app ((X.reduction A I).obj F) ≫
        (f.push A).map ((X.finiteEvaluationIso A I n).hom.app F) ≫
        (f.finiteRestrictionPushIso A I n).hom.app ((X.finiteReduction A I n).obj F) =
      (Y.finiteEvaluationIso A I n).hom.app ((f.push A).obj F) ≫
        (Y.finiteRestriction A I n).map (f.finiteProjection A I n F)) := by
  obtain ⟨p, d, _, _, hd, hf, he, hi, hfi, hu⟩ :=
    PerfectQuotientExchange.perfectQuotientExchangeNormalization (f := f) hperfect
  have hs (F : X.derived A) :
      IsIso ((PerfectQuotientExchange.strictExchange p).app F) := by
    rw [← hd F]
    have : IsIso (PerfectQuotientExchange.exchange p) := hi
    infer_instance
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F
    have h := hs F
    rw [strict_exchange_eq] at h
    have : IsIso (f.towerProjection A I F ≫
        (f.towerPush A).map (p.reductionX.tower.inv.app F)) :=
      IsIso.of_isIso_comp_left (p.reductionY.tower.hom.app ((f.push A).obj F)) _
    exact IsIso.of_isIso_comp_right _ ((f.towerPush A).map (p.reductionX.tower.inv.app F))
  · intro n F
    rw [← hf F n]
    have := hfi n
    infer_instance
  · intro F
    simpa only [completion_exchange_eq, Category.assoc] using hu F
  · intro F n
    have h := he F n
    rw [strict_exchange_eq, hf F n] at h
    simp only [Functor.map_comp, Category.assoc] at h
    apply (cancel_epi ((Y.evaluate A n).map
      (p.reductionY.tower.hom.app ((f.push A).obj F)))).1
    have hc : (Y.evaluate A n).map ((f.towerPush A).map (p.reductionX.tower.inv.app F)) ≫
        (Y.evaluate A n).map ((f.towerPush A).map (p.reductionX.tower.hom.app F)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
        Functor.map_id, Functor.map_id]
    rw [reassoc_of% hc] at h
    simpa only [Category.id_comp] using h

omit [IsNoetherianRing A] in
private theorem finite_equation_from_projection
    (o : TensorData f A) (s : ∀ n : ℕ, FiniteTensor (I := I) o n)
    (hp : ∀ (n : ℕ) (H : X.derived A) (K : Y.derived A),
      (s n).projection H K =
        (Y.finiteReduction A I n).map (o.projection H K) ≫
          f.finiteProjection A I n (o.tensorX.obj (H, (f.pull A).obj K)))
    (he : ∀ (F : X.derived A) (n : ℕ),
      (Y.evaluate A n).map (f.towerProjection A I F) ≫
        (f.evaluatePushIso A n).hom.app ((X.reduction A I).obj F) ≫
        (f.push A).map ((X.finiteEvaluationIso A I n).hom.app F) ≫
        (f.finiteRestrictionPushIso A I n).hom.app ((X.finiteReduction A I n).obj F) =
      (Y.finiteEvaluationIso A I n).hom.app ((f.push A).obj F) ≫
        (Y.finiteRestriction A I n).map (f.finiteProjection A I n F)) :
    o.FiniteEquation s := by
  intro n H K
  dsimp only [TensorData.towerProjection]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [he]
  have hn := (Y.finiteEvaluationIso A I n).hom.naturality (o.projection H K)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ← hp]

private theorem tensor_data_exists (f : Morphism Y X) (A : Type u) [CommRing A] :
    Nonempty (TensorData f A) := by
  let := f.finiteLimits
  let ty := constantDerivedTensor Y.topology A
  let tx := constantDerivedTensor X.topology A
  let my := native_tensor_model Y A
  let mx := native_tensor_model X A
  have hm : ∀ {M N : Y.modules A} (h : M ⟶ N),
      (f.modulePull A).map h = eqToHom (show (f.modulePull A).obj M =
        changeOfRings (constantMap f.algebra A) ((f.algebra.algebra (Y.ring A)).modules.obj M)
        from rfl) ≫ changeOfRingsHom (constantMap f.algebra A) _
          ((f.algebra.algebra (Y.ring A)).modules.map h) ≫ eqToHom (by rfl) := by
    intro M N h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨c⟩ := canonicalRingedTensorComparison_nonempty (Y.ring A) (X.ring A)
    (f.algebra.rings.obj (Y.ring A)) f.inverse (f.algebra.algebra (Y.ring A))
    (constantMap f.algebra A) (f.modulePull A) (fun _ ↦ rfl) f.direct f.adjunction hm
  let e : RingedTensorEdge (corner Y A ty) (corner X A tx) := {
    inverse := f.inverse
    direct := f.direct
    adjunction := f.adjunction
    inverseRing := f.algebra.rings.obj (Y.ring A)
    algebraic := f.algebra.algebra (Y.ring A)
    ringMap := constantMap f.algebra A
    pullback := f.modulePull A
    object_eq := fun _ ↦ rfl
    map_eq := hm
    ordinaryTensor := c
    pushforward := f.modulePush A
    moduleAdjunction := f.moduleAdjunction A
    left := f.pull A
    epsilon := (f.modulePull A).mapDerivedCategoryFactorsh.hom
    isLeftDerived := inferInstance
    right := f.push A
    derivedAdjunction := f.adj A }
  exact ⟨{
    tensorY := ty, tensorX := tx, modelY := my, modelX := mx, edge := e
    inverse_eq := rfl, direct_eq := rfl, adjunction_eq := HEq.rfl
    inverseRing_eq := rfl, algebra_eq := HEq.rfl, ringMap_eq := HEq.rfl
    pullback_eq := rfl, pushforward_eq := rfl, moduleAdjunction_eq := HEq.rfl
    left_eq := rfl, right_eq := rfl, epsilon_eq := HEq.rfl
    derivedAdjunction_eq := HEq.rfl
    comparison := e.tensorComparison my mx, comparison_eq := HEq.rfl }⟩

omit [IsNoetherianRing A] in
private theorem scalar_tensor_exists (T : Site.{u}) (n : ℕ)
    (t : T.derived A × T.derived A ⥤ T.derived A)
    (tn : T.derived (quotientRing A I n) × T.derived (quotientRing A I n) ⥤
      T.derived (quotientRing A I n))
    (m : RingedTensorModel (corner T A t))
    (mn : RingedTensorModel (corner T (quotientRing A I n) tn)) :
    ∃ s : ScalarTensor (I := I) T n t tn, s.Normalized m mn ∧
      (∀ M : T.modules A, HEq (s.edge.insertion M)
        (insertion (quotient T.topology A I n) M)) ∧
      ∀ P : Cx (T.ring A), HEq
        (derivedPullbackComplexComparison s.edge.pullback s.edge.left s.edge.epsilon P)
        ((extendComparison (quotient T.topology A I n)).app P) := by
  let φ := quotient T.topology A I n
  let alg := CochainPullback.identityAlgebraicInverseImage (T.ring A)
  have hm : ∀ {M N : T.modules A} (h : M ⟶ N),
      (change φ).map h = eqToHom (show (change φ).obj M =
        changeOfRings φ (alg.modules.obj M) from rfl) ≫
          changeOfRingsHom φ (alg.modules.obj M) (alg.modules.map h) ≫
            eqToHom (by rfl) := by
    intro M N h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨c⟩ := canonicalRingedTensorComparison_nonempty (T.ring A)
    (T.ring (quotientRing A I n)) (T.ring A) (𝟭 _) alg φ (change φ)
    (fun _ ↦ rfl) (𝟭 _) Adjunction.id hm
  obtain ⟨ε, hε, hc⟩ := exists_homotopy_leftDerived_comparison
    (change φ) (extend φ) (extendComparison φ) (derivedExtension φ).universal
  have hc' (P : Cx (T.ring A)) :
      derivedPullbackComplexComparison (change φ) (extend φ) ε P =
        (extendComparison φ).app P :=
    (SheafOfModules.mateDerivedComplexComparisonApp (change φ) (extend φ) ε P).trans (hc P)
  let e : RingedTensorEdge (corner T A t) (corner T (quotientRing A I n) tn) := {
    inverse := 𝟭 _
    direct := 𝟭 _
    adjunction := Adjunction.id
    inverseRing := T.ring A
    algebraic := alg
    ringMap := φ
    pullback := change φ
    object_eq := fun _ ↦ rfl
    map_eq := hm
    ordinaryTensor := c
    pushforward := res φ
    moduleAdjunction := T.finiteModuleAdjunction A I n
    left := extend φ
    epsilon := ε
    isLeftDerived := hε
    right := T.finiteRestriction A I n
    derivedAdjunction := T.finiteAdjunction A I n }
  refine ⟨{
    edge := e
    inverse_eq := rfl, direct_eq := rfl, adjunction_eq := HEq.rfl
    inverseRing_eq := rfl, ringUnderlying_eq := HEq.rfl, ringMap_eq := HEq.rfl
    pullback_eq := rfl, pushforward_eq := rfl, left_eq := rfl, right_eq := rfl
    moduleAdjunction_eq := HEq.rfl, derivedAdjunction_eq := HEq.rfl
    left_normalization := ?_
    balancing := e.tensorComparison m mn }, HEq.rfl, ?_, ?_⟩
  · intro P _ _
    exact heq_of_eq (hc' P)
  · intro M
    apply heq_of_eq
    change 𝟙 _ ≫ c.q M = insertion φ M
    rw [Category.id_comp]
    apply (insertion_existsUnique φ M).unique
    · intro U x
      exact (c.q_one M U x).trans (by rfl)
    · exact (insertion_existsUnique φ M).exists.choose_spec
  · intro P
    exact heq_of_eq (hc' P)

omit [IsNoetherianRing A] in
private theorem tensor_insertion (o : TensorData f A) (M : Y.modules A) :
    HEq (o.edge.insertion M) (pullInsertion f.algebra (constantMap f.algebra A) M) := by
  rcases o with ⟨ty, tx, my, mx, e, hi, hd, ha, hr, hal, hc,
    hpb, hpf, hma, hl, hri, he, hda, cmp, hcmp⟩
  rcases e with @⟨inv, dir, adj, hfin, R, alg, φ, pb, hobj, hmap, hadd,
    ot, pf, ma, L, ε, hle, Rf, da⟩
  dsimp only at hi hd ha hr hal hc hpb hpf hma hl hri he hda hcmp ⊢
  subst_vars
  cases hal
  cases hc
  dsimp only [RingedTensorEdge.insertion, pullInsertion]
  apply heq_of_eq
  congr 1
  apply (insertion_existsUnique _ _).unique
  · intro U m
    exact (ot.q_one M U m).trans (by rfl)
  · exact (insertion_existsUnique _ _).exists.choose_spec

private theorem exact_pullback_comparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    derivedPullbackComplexComparison F F.mapDerivedCategory F.mapDerivedCategoryFactorsh.hom P =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [SheafOfModules.mateDerivedComplexComparisonApp, Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app P ≫
    𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  simp only [Functor.map_id, Category.id_comp]
  exact Category.comp_id _

private theorem cancel_mapped_iso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M N : C} (e : M ≅ N) {U V : D} (a : U ⟶ V) (b : V ⟶ F.obj M)
    (c : U ⟶ F.obj N) (h : a ≫ b ≫ F.map e.hom = c) :
    a ≫ b = c ≫ F.map e.inv := by
  rw [← h, Category.assoc, Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, Category.comp_id]

omit [IsNoetherianRing A] in
private theorem finite_square_of_normalized
    {ty : Y.derived A × Y.derived A ⥤ Y.derived A}
    {tx : X.derived A × X.derived A ⥤ X.derived A} (n : ℕ)
    {tyn : Y.derived (quotientRing A I n) × Y.derived (quotientRing A I n) ⥤
      Y.derived (quotientRing A I n)}
    {txn : X.derived (quotientRing A I n) × X.derived (quotientRing A I n) ⥤
      X.derived (quotientRing A I n)}
    (e : RingedTensorEdge (corner Y A ty) (corner X A tx))
    (ey : RingedTensorEdge (corner Y A ty) (corner Y (quotientRing A I n) tyn))
    (ex : RingedTensorEdge (corner X A tx) (corner X (quotientRing A I n) txn))
    (en : RingedTensorEdge (corner Y (quotientRing A I n) tyn)
      (corner X (quotientRing A I n) txn))
    (hi : e.inverse = f.inverse) (hiy : ey.inverse = 𝟭 _)
    (hix : ex.inverse = 𝟭 _) (hin : en.inverse = f.inverse)
    (hp : e.pullback = f.modulePull A)
    (hpy : ey.pullback = change (quotient Y.topology A I n))
    (hpx : ex.pullback = change (quotient X.topology A I n))
    (hpn : en.pullback = f.modulePull (quotientRing A I n))
    (ho : ∀ M : Y.modules A, HEq (e.insertion M)
      (pullInsertion f.algebra (constantMap f.algebra A) M))
    (hoy : ∀ M : Y.modules A, HEq (ey.insertion M)
      (insertion (quotient Y.topology A I n) M))
    (hox : ∀ M : X.modules A, HEq (ex.insertion M)
      (insertion (quotient X.topology A I n) M))
    (hon : ∀ M : Y.modules (quotientRing A I n), HEq (en.insertion M)
      (pullInsertion f.algebra (constantMap f.algebra (quotientRing A I n)) M)) :
    ∃ s : RingedTensorSquare (corner Y A ty) (corner X A tx)
      (corner Y (quotientRing A I n) tyn) (corner X (quotientRing A I n) txn)
      e ey ex en,
      HEq s.modules (ordinaryFinitePull f.algebra f.direct f.adjunction A I n).symm := by
  rcases e with @⟨inv, dir, adj, hfin, R, alg, φ, pb, hobj, hmap, hadd,
    ot, pf, ma, L, ε, hle, Rf, da⟩
  rcases en with @⟨invn, dirn, adjn, hfinn, Rn, algn, φn, pbn, hobjn, hmapn, haddn,
    otn, pfn, man, Ln, εn, hlen, Rfn, dan⟩
  rcases ey with @⟨invy, diry, adjy, hfiny, Ry, algy, φy, pby, hobjy, hmapy, haddy,
    oty, pfy, may, Ly, εy, hley, Rfy, day⟩
  rcases ex with @⟨invx, dirx, adjx, hfinx, Rx, algx, φx, pbx, hobjx, hmapx, haddx,
    otx, pfx, max, Lx, εx, hlex, Rfx, dax⟩
  dsimp only at hi hiy hix hin hp hpy hpx hpn
  subst_vars
  refine ⟨⟨Iso.refl _, (ordinaryFinitePull f.algebra f.direct f.adjunction A I n).symm,
    ?_⟩, HEq.rfl⟩
  intro M
  have he := (ordinaryFinitePull_existsUnique f.algebra f.direct f.adjunction A I n
    ).exists.choose_spec M
  have h₀ := eq_of_heq (ho M)
  have h₁ := eq_of_heq (hoy M)
  have h₂ := eq_of_heq (hox ((f.modulePull A).obj M))
  have h₃ := eq_of_heq (hon ((change (quotient Y.topology A I n)).obj M))
  dsimp only [Functor.id_map, Iso.refl_hom, NatTrans.id_app, Iso.symm_hom]
  rw [h₀, h₁, h₂, h₃, Category.id_comp]
  change pullInsertion _ _ M ≫ insertion _ _ ≫
    (underlying (finite X.topology A I n)).map
      ((ordinaryFinitePull f.algebra f.direct f.adjunction A I n).hom.app M) = _ at he
  exact (cancel_mapped_iso (underlying (finite X.topology A I n))
    ((ordinaryFinitePull f.algebra f.direct f.adjunction A I n).app M) _ _ _ he).symm

private theorem iso_eq_inverse
    {C : Type*} [Category C] {U V : C} (θ : U ≅ V) (χ : V ≅ U)
    (h : θ.symm = χ) : θ = χ.symm := congrArg Iso.symm h

private theorem reverse_mapped_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : D ⥤ E) {F G : C ⥤ E} (θ : F ≅ G) (x : C)
    {R S : E} {M N : D} (j : M ≅ N)
    (a₁ : G.obj x ⟶ R) (a₂ : R ⟶ Q.obj M)
    (b₁ : F.obj x ⟶ S) (b₂ : S ⟶ Q.obj N)
    (h : θ.hom.app x ≫ a₁ ≫ a₂ = b₁ ≫ b₂ ≫ Q.map j.inv) :
    a₁ ≫ a₂ ≫ Q.map j.hom = θ.inv.app x ≫ b₁ ≫ b₂ := by
  apply (cancel_mono (Q.map j.inv)).1
  simp only [Category.assoc, ← Q.map_comp, Iso.hom_inv_id, Q.map_id, Category.comp_id]
  rw [← h, Iso.inv_hom_id_app_assoc]

section NormalizationTransport
variable {B E B' E' : Type*} [Category B] [Category E] [Category B'] [Category E']
  [Abelian B] [Abelian E] [Abelian B'] [Abelian E']
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
  [HasDerivedCategory.{w} B'] [HasDerivedCategory.{w} E']

private def SquareNormalization
    (P : ObjectProperty (CochainComplex B ℤ))
    (F : B ⥤ E) (G : B ⥤ B') (J : E ⥤ E') (N : B' ⥤ E')
    [F.Additive] [G.Additive] [J.Additive] [N.Additive]
    (LF : DerivedCategory B ⥤ DerivedCategory E)
    (LG : DerivedCategory B ⥤ DerivedCategory B')
    (LJ : DerivedCategory E ⥤ DerivedCategory E')
    (LN : DerivedCategory B' ⥤ DerivedCategory E')
    (cF : ∀ K, LF.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (cG : ∀ K, LG.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj K))
    (cJ : ∀ K, LJ.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((J.mapHomologicalComplex (.up ℤ)).obj K))
    (cN : ∀ K, LN.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((N.mapHomologicalComplex (.up ℤ)).obj K))
    (j : G.mapHomologicalComplex (.up ℤ) ⋙ N.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ J.mapHomologicalComplex (.up ℤ))
    (θ : LG ⋙ LN ≅ LF ⋙ LJ) : Prop :=
  ∀ K : CochainComplex B ℤ, P K →
    θ.hom.app (DerivedCategory.Q.obj K) ≫ LJ.map (cF K) ≫
      cJ ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    LN.map (cG K) ≫ cN ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map (j.hom.app K)

private theorem square_normalization_transport
    (P : ObjectProperty (CochainComplex B ℤ))
    (F F₀ : B ⥤ E) (G G₀ : B ⥤ B') (J J₀ : E ⥤ E') (N N₀ : B' ⥤ E')
    [F.Additive] [F₀.Additive] [G.Additive] [G₀.Additive]
    [J.Additive] [J₀.Additive] [N.Additive] [N₀.Additive]
    (hF : F = F₀) (hG : G = G₀) (hJ : J = J₀) (hN : N = N₀)
    (LF LF₀ : DerivedCategory B ⥤ DerivedCategory E)
    (LG LG₀ : DerivedCategory B ⥤ DerivedCategory B')
    (LJ LJ₀ : DerivedCategory E ⥤ DerivedCategory E')
    (LN LN₀ : DerivedCategory B' ⥤ DerivedCategory E')
    (hLF : LF = LF₀) (hLG : LG = LG₀) (hLJ : LJ = LJ₀) (hLN : LN = LN₀)
    (cF : ∀ K, LF.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (cF₀ : ∀ K, LF₀.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F₀.mapHomologicalComplex (.up ℤ)).obj K))
    (hcF : HEq cF cF₀)
    (cG : ∀ K, LG.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj K))
    (cG₀ : ∀ K, LG₀.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((G₀.mapHomologicalComplex (.up ℤ)).obj K))
    (hcG : HEq cG cG₀)
    (cJ : ∀ K, LJ.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((J.mapHomologicalComplex (.up ℤ)).obj K))
    (cJ₀ : ∀ K, LJ₀.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((J₀.mapHomologicalComplex (.up ℤ)).obj K))
    (hcJ : HEq cJ cJ₀)
    (cN : ∀ K, LN.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((N.mapHomologicalComplex (.up ℤ)).obj K))
    (cN₀ : ∀ K, LN₀.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((N₀.mapHomologicalComplex (.up ℤ)).obj K))
    (hcN : HEq cN cN₀)
    (j : G.mapHomologicalComplex (.up ℤ) ⋙ N.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ J.mapHomologicalComplex (.up ℤ))
    (j₀ : G₀.mapHomologicalComplex (.up ℤ) ⋙ N₀.mapHomologicalComplex (.up ℤ) ≅
      F₀.mapHomologicalComplex (.up ℤ) ⋙ J₀.mapHomologicalComplex (.up ℤ))
    (hj : HEq j j₀) (θ : LG ⋙ LN ≅ LF ⋙ LJ)
    (h : SquareNormalization P F G J N LF LG LJ LN cF cG cJ cN j θ) :
    ∃ θ₀ : LG₀ ⋙ LN₀ ≅ LF₀ ⋙ LJ₀, HEq θ θ₀ ∧
      SquareNormalization P F₀ G₀ J₀ N₀ LF₀ LG₀ LJ₀ LN₀ cF₀ cG₀ cJ₀ cN₀ j₀ θ₀ := by
  subst_vars
  exact ⟨θ, HEq.rfl, h⟩

private theorem comparison_family_transport
    (F F₀ : B ⥤ E) [F.Additive] [F₀.Additive]
    (L L₀ : DerivedCategory B ⥤ DerivedCategory E)
    (hF : F = F₀) (hL : L = L₀)
    (c : ∀ K, L.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (c₀ : ∀ K, L₀.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F₀.mapHomologicalComplex (.up ℤ)).obj K))
    (h : ∀ K, HEq (c K) (c₀ K)) : HEq c c₀ := by
  subst_vars
  exact heq_of_eq (funext fun K ↦ eq_of_heq (h K))

private theorem exact_comparison_transport
    (F F₀ : B ⥤ E) [F.Additive] [F₀.Additive]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    (L : DerivedCategory B ⥤ DerivedCategory E)
    (hF : F = F₀) (hL : L = F₀.mapDerivedCategory)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (he : HEq ε F₀.mapDerivedCategoryFactorsh.hom) :
    HEq (derivedPullbackComplexComparison F L ε)
      (fun K ↦ F₀.mapDerivedCategoryFactors.hom.app K) := by
  subst_vars
  apply heq_of_eq
  funext K
  exact exact_pullback_comparison F₀ K

omit [HasDerivedCategory B] [HasDerivedCategory E]
  [HasDerivedCategory B'] [HasDerivedCategory E'] in
private theorem complex_square_transport
    (F F₀ : B ⥤ E) (G G₀ : B ⥤ B') (J J₀ : E ⥤ E') (N N₀ : B' ⥤ E')
    [F.Additive] [F₀.Additive] [G.Additive] [G₀.Additive]
    [J.Additive] [J₀.Additive] [N.Additive] [N₀.Additive]
    (hF : F = F₀) (hG : G = G₀) (hJ : J = J₀) (hN : N = N₀)
    (j : G ⋙ N ≅ F ⋙ J) (j₀ : F₀ ⋙ J₀ ≅ G₀ ⋙ N₀) (hj : HEq j j₀.symm) :
    HEq (show G.mapHomologicalComplex (.up ℤ) ⋙ N.mapHomologicalComplex (.up ℤ) ≅
        F.mapHomologicalComplex (.up ℤ) ⋙ J.mapHomologicalComplex (.up ℤ)
      from NatIso.mapHomologicalComplex j (.up ℤ))
      (mapComplexSquare F₀ J₀ G₀ N₀ j₀).symm := by
  subst_vars
  unfold mapComplexSquare
  rfl

end NormalizationTransport

omit [IsNoetherianRing A] in
private theorem finite_normalization_unique (n : ℕ)
    (θ : Y.finiteReduction A I n ⋙ f.pull (quotientRing A I n) ≅
      f.pull A ⋙ X.finiteReduction A I n)
    (hθ : SquareNormalization
      (fun P : Cx (Y.ring A) ↦ P.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, (P.X q).IsFlat)
      (f.modulePull A) (change (quotient Y.topology A I n))
      (change (quotient X.topology A I n)) (f.modulePull (quotientRing A I n))
      (f.pull A) (Y.finiteReduction A I n) (X.finiteReduction A I n)
      (f.pull (quotientRing A I n))
      (fun P ↦ (f.modulePull A).mapDerivedCategoryFactors.hom.app P)
      (fun P ↦ (extendComparison (quotient Y.topology A I n)).app P)
      (fun P ↦ (extendComparison (quotient X.topology A I n)).app P)
      (fun P ↦ (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom.app P)
      (mapComplexSquare (f.modulePull A) (change (quotient X.topology A I n))
        (change (quotient Y.topology A I n)) (f.modulePull (quotientRing A I n))
        (ordinaryFinitePull f.algebra f.direct f.adjunction A I n)).symm θ) :
    θ = (f.finitePullIso A I n).symm := by
  have hθ' : θ.symm = f.finitePullIso A I n := by
    apply (f.finitePullIso_existsUnique A I n).unique
    · intro P hk hf
      have ht := hθ P ⟨hk, hf⟩
      dsimp only [SquareNormalization, Iso.symm_hom] at ht
      exact reverse_mapped_comparison (Q (X.ring (quotientRing A I n)))
        θ (DerivedCategory.Q.obj P)
        ((mapComplexSquare (f.modulePull A) (change (quotient X.topology A I n))
          (change (quotient Y.topology A I n)) (f.modulePull (quotientRing A I n))
          (ordinaryFinitePull f.algebra f.direct f.adjunction A I n)).app P)
        ((X.finiteReduction A I n).map
          ((f.modulePull A).mapDerivedCategoryFactors.hom.app P))
        ((extendComparison (quotient X.topology A I n)).app
          (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P))
        ((f.pull (quotientRing A I n)).map
          ((extendComparison (quotient Y.topology A I n)).app P))
        ((f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom.app
          (((change (quotient Y.topology A I n)).mapHomologicalComplex (.up ℤ)).obj P)) ht
    · exact (f.finitePullIso_existsUnique A I n).exists.choose_spec
  exact iso_eq_inverse θ (f.finitePullIso A I n) hθ'

omit [IsNoetherianRing A] in
private theorem finite_derived_square
    {ty : Y.derived A × Y.derived A ⥤ Y.derived A}
    {tx : X.derived A × X.derived A ⥤ X.derived A} (n : ℕ)
    {tyn : Y.derived (quotientRing A I n) × Y.derived (quotientRing A I n) ⥤
      Y.derived (quotientRing A I n)}
    {txn : X.derived (quotientRing A I n) × X.derived (quotientRing A I n) ⥤
      X.derived (quotientRing A I n)}
    (e : RingedTensorEdge (corner Y A ty) (corner X A tx))
    (ey : RingedTensorEdge (corner Y A ty) (corner Y (quotientRing A I n) tyn))
    (ex : RingedTensorEdge (corner X A tx) (corner X (quotientRing A I n) txn))
    (en : RingedTensorEdge (corner Y (quotientRing A I n) tyn)
      (corner X (quotientRing A I n) txn))
    (hp : e.pullback = f.modulePull A)
    (hpy : ey.pullback = change (quotient Y.topology A I n))
    (hpx : ex.pullback = change (quotient X.topology A I n))
    (hpn : en.pullback = f.modulePull (quotientRing A I n))
    (hl : e.left = f.pull A) (hly : ey.left = Y.finiteReduction A I n)
    (hlx : ex.left = X.finiteReduction A I n)
    (hln : en.left = f.pull (quotientRing A I n))
    (he : HEq e.epsilon (f.modulePull A).mapDerivedCategoryFactorsh.hom)
    (hen : HEq en.epsilon
      (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactorsh.hom)
    (hny : ∀ P : Cx (Y.ring A),
      HEq (derivedPullbackComplexComparison ey.pullback ey.left ey.epsilon P)
        ((extendComparison (quotient Y.topology A I n)).app P))
    (hnx : ∀ P : Cx (X.ring A),
      HEq (derivedPullbackComplexComparison ex.pullback ex.left ex.epsilon P)
        ((extendComparison (quotient X.topology A I n)).app P))
    (sq : RingedTensorSquare (corner Y A ty) (corner X A tx)
      (corner Y (quotientRing A I n) tyn) (corner X (quotientRing A I n) txn)
      e ey ex en)
    (hm : HEq sq.modules (ordinaryFinitePull f.algebra f.direct f.adjunction A I n).symm) :
    HEq sq.derivedComparison (f.finitePullIso A I n).symm := by
  let := e.additive
  let := ey.additive
  let := ex.additive
  let := en.additive
  let := f.modulePull_finiteLimits A
  let := f.modulePull_finiteColimits A
  let := f.modulePull_finiteLimits (quotientRing A I n)
  let := f.modulePull_finiteColimits (quotientRing A I n)
  have hcF : HEq (derivedPullbackComplexComparison e.pullback e.left e.epsilon)
      (fun P ↦ (f.modulePull A).mapDerivedCategoryFactors.hom.app P) := by
    exact exact_comparison_transport e.pullback (f.modulePull A) e.left hp hl e.epsilon he
  have hcN : HEq (derivedPullbackComplexComparison en.pullback en.left en.epsilon)
      (fun P ↦ (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom.app P) := by
    exact exact_comparison_transport en.pullback
      (f.modulePull (quotientRing A I n)) en.left hpn hln en.epsilon hen
  have hcG : HEq (derivedPullbackComplexComparison ey.pullback ey.left ey.epsilon)
      (fun P ↦ (extendComparison (quotient Y.topology A I n)).app P) := by
    exact comparison_family_transport ey.pullback (change (quotient Y.topology A I n))
      ey.left (Y.finiteReduction A I n) hpy hly
      (derivedPullbackComplexComparison ey.pullback ey.left ey.epsilon)
      (fun P ↦ (extendComparison (quotient Y.topology A I n)).app P) hny
  have hcJ : HEq (derivedPullbackComplexComparison ex.pullback ex.left ex.epsilon)
      (fun P ↦ (extendComparison (quotient X.topology A I n)).app P) := by
    exact comparison_family_transport ex.pullback (change (quotient X.topology A I n))
      ex.left (X.finiteReduction A I n) hpx hlx
      (derivedPullbackComplexComparison ex.pullback ex.left ex.epsilon)
      (fun P ↦ (extendComparison (quotient X.topology A I n)).app P) hnx
  have hj' := complex_square_transport e.pullback (f.modulePull A)
    ey.pullback (change (quotient Y.topology A I n))
    ex.pullback (change (quotient X.topology A I n))
    en.pullback (f.modulePull (quotientRing A I n)) hp hpy hpx hpn
    sq.modules (ordinaryFinitePull f.algebra f.direct f.adjunction A I n) hm
  obtain ⟨θ₀, hθ₀, hn₀⟩ := square_normalization_transport
      (B := Y.modules A) (E := X.modules A)
      (B' := Y.modules (quotientRing A I n)) (E' := X.modules (quotientRing A I n))
      (fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, (P.X q).IsFlat)
      e.pullback (f.modulePull A) ey.pullback (change (quotient Y.topology A I n))
      ex.pullback (change (quotient X.topology A I n))
      en.pullback (f.modulePull (quotientRing A I n)) hp hpy hpx hpn
      e.left (f.pull A) ey.left (Y.finiteReduction A I n)
      ex.left (X.finiteReduction A I n) en.left (f.pull (quotientRing A I n))
      hl hly hlx hln _ _ hcF _ _ hcG _ _ hcJ _ _ hcN
      sq.complexComparison _ hj' sq.derivedComparison
      (by
        intro P hP
        exact sq.derivedComparison_existsUnique.exists.choose_spec P hP.1 hP.2)
  have hθeq := finite_normalization_unique n θ₀ hn₀
  exact hθ₀.trans (heq_of_eq hθeq)

omit [IsNoetherianRing A] in
/-- Finite scalar extension preserves the counit-defined projection mate.
Source: Stacks 07A4 and 0B56
(blueprint: lem-pur-compact-support-completed-projection-coherence).
Proof: form the ringed square with the two quotient ring maps and the original
inverse image on its horizontal sides. The ordinary square is the inverse of
ordinaryFinitePull, as follows by postcomposing its insertion equation with its
inverse. On flat-term K-flat complexes, the normalization of finitePullIso says
that the derived square is its inverse. Apply ringedExchangeTensorCoherence and
postcompose with the inverse of targetBalancing. The exchange components are the
finite coefficient counit mates, so its equality is exactly the displayed one. -/
private theorem finite_tensor_projection_coherence (o : TensorData f A) (n : ℕ) :
    ∃ s : FiniteTensor (I := I) o n, ∀ (H : X.derived A) (K : Y.derived A),
      s.projection H K = (Y.finiteReduction A I n).map (o.projection H K) ≫
        f.finiteProjection A I n (o.tensorX.obj (H, (f.pull A).obj K)) := by
  obtain ⟨on⟩ := tensor_data_exists f (quotientRing A I n)
  obtain ⟨sy, hy, hsy, hεy⟩ := scalar_tensor_exists (I := I) Y n o.tensorY on.tensorY
    o.modelY on.modelY
  obtain ⟨sx, hx, hsx, hεx⟩ := scalar_tensor_exists (I := I) X n o.tensorX on.tensorX
    o.modelX on.modelX
  obtain ⟨sq, hsq⟩ := finite_square_of_normalized (f := f) n o.edge sy.edge sx.edge on.edge
    o.inverse_eq sy.inverse_eq sx.inverse_eq on.inverse_eq
    o.pullback_eq sy.pullback_eq sx.pullback_eq on.pullback_eq
    (tensor_insertion o) hsy hsx (tensor_insertion on)
  have hθ := finite_derived_square n o.edge sy.edge sx.edge on.edge
    o.pullback_eq sy.pullback_eq sx.pullback_eq on.pullback_eq
    o.left_eq sy.left_eq sx.left_eq on.left_eq o.epsilon_eq on.epsilon_eq
    hεy hεx sq hsq
  let s : FiniteTensor (I := I) o n := ⟨on, sy, sx, hy, hx⟩
  exact ⟨s, finite_projection_square o n s sq hθ⟩

end Proofs

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
  classical
  obtain ⟨b⟩ := completed_tensor_exists (I := I) o
  choose s hs using fun n ↦ finite_tensor_projection_coherence (I := I) o n
  obtain ⟨hi, hfi, hρ, he⟩ := perfect_exchange_properties (f := f) _hperfect
  have hu := completed_unit_equation b
  have huniq := completed_unique b hu
  refine ⟨b, (fun n ↦ (s n)), hi, hfi, hu, huniq, completed_limit b huniq hρ, ?_,
    transpose_compatibility f A, completed_natural b hu⟩
  exact finite_equation_from_projection o (fun n ↦ s n)
    (fun n H K ↦ hs n H K) he

end CategoryTheory.AdicSites.ProjectionCoherence
