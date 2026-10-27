/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.CompletedCoefficientTensorTransportModels
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedCoefficientPushforwardComparison
public import Sheaf.Paper.CompletedOperationTowerSubstitution
public import Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit
public import Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Normalized monoidal and adjunction transport for completed coefficients

Source: Stacks Project, algebraization.tex, Tags 099I and 099K; main-20261015,
lem-fix-operation-reduction.proof.md, final paragraph. The combined assertion and
its representative normalizations are taken from the dispatched transport item's proof
(blueprint: def-pur-completed-coefficient-adjunction-transport-models).

The records below present canonical constructions, including their localization,
completion-unit and sectionwise normalizations. Their existence is a conclusion;
no tensor comparison, adjunction or preservation assertion is an extra hypothesis.
Sites have object universe t+1 and morphism universe t, independently of E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open WeilConjectures
namespace WeilConjectures.CompletedCoefficientTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Constant-coefficient direct image is additive section by section.
Source: Stacks 03D2
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
instance constantPushAdditive {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (CompletedCoefficientPushforward.push.{t, u} f
      (CompletedCoefficientPushforward.constantStructure l E f)).Additive where
  map_add := by intros; rfl

/-- Ordinary and derived pullback/direct-image adjunctions, with the universal
K-flat/K-injective Hom normalization. The right images and their scalar square are
exactly the recorded pushforward-comparison data, including their actual units.
Source: node proof steps 5 and 8
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
structure Arrow {X Y : Scheme.{t}} (SX : Site l E X) (SY : Site l E Y) (f : X ⟶ Y) where
  image : CompletedCoefficientPushforward.ComparisonData l E f
  sourceU : image.source.U = SX.U
  targetU : image.target.U = SY.U
  ordinaryR : CompletedCoefficientPushforward.Mod Y
      (completedIntegralCoefficientSheafUnrestricted l E Y) ⥤
    CompletedCoefficientPushforward.Mod X (completedIntegralCoefficientSheafUnrestricted l E X)
  ordinaryA : CompletedCoefficientPushforward.Mod Y (integralConstantRingOfUniverses l E Y) ⥤
    CompletedCoefficientPushforward.Mod X (integralConstantRingOfUniverses l E X)
  [ordinaryRAdditive : ordinaryR.Additive]
  [ordinaryAAdditive : ordinaryA.Additive]
  adjR : ordinaryR ⊣ CompletedCoefficientPushforward.push.{t, u} f image.structureMap
  adjA : ordinaryA ⊣ CompletedCoefficientPushforward.push.{t, u} f
    (CompletedCoefficientPushforward.constantStructure l E f)
  r : CategoryTheory.RingedCoefficientCounit.DerivedAdjunction ordinaryR
    (CompletedCoefficientPushforward.push.{t, u} f image.structureMap) adjR
  a : CategoryTheory.RingedCoefficientCounit.DerivedAdjunction ordinaryA
    (CompletedCoefficientPushforward.push.{t, u} f
      (CompletedCoefficientPushforward.constantStructure l E f)) adjA
  r_right : r.right = image.completedImage.functor
  r_unit : HEq r.eta image.completedImage.unit
  a_right : a.right = image.constantImage.functor
  a_unit : HEq a.eta image.constantImage.unit
  exactA : IsIso a.epsilon
  flatR : ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
    IsIso (r.epsilon.app P.obj)
  pullback : r.left ⋙ IntegralOnSlice.completion l E X none ≅ integralDerivedPullback l E f

attribute [instance] Arrow.ordinaryRAdditive Arrow.ordinaryAAdditive

/-- The canonical derived-composition comparison, transported only along equalities
of its normalized universal derived models.
Source: node proof step 8; Stacks 0D6E
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.kappa {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y} {f : X ⟶ Y}
    (F : Arrow l E SX SY f) : F.r.right ⋙ SY.U.functor ≅ SX.U.functor ⋙ F.a.right :=
  Functor.isoWhiskerRight (eqToIso F.r_right) SY.U.functor ≪≫
    Functor.isoWhiskerLeft F.image.completedImage.functor
      (eqToIso (congrArg CompletedCoefficientPushforward.ExactImage.functor F.targetU)).symm ≪≫
    F.image.constantSquare.comparison ≪≫
    Functor.isoWhiskerRight
      (eqToIso (congrArg CompletedCoefficientPushforward.ExactImage.functor F.sourceU))
      F.image.constantImage.functor ≪≫
    Functor.isoWhiskerLeft SX.U.functor (eqToIso F.a_right).symm

/-- The scalar-unit map is the mate of the sectionwise identity coefficient square.
This is the canonical map x ↦ 1 ⊗ x under the ringed pullback adjunction.
Source: Stacks 03D7; node proof step 5
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.scalarUnit {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y} {f : X ⟶ Y}
    (F : Arrow l E SX SY f)
    (M : CompletedCoefficientPushforward.Mod Y
      (completedIntegralCoefficientSheafUnrestricted l E Y)) :
    F.ordinaryA.obj ((SheafOfModules.restrictScalars
      (integralConstantToCompletionOfUniverses l E Y)).obj M) ⟶
    (SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E X)).obj
      (F.ordinaryR.obj M) :=
  (F.adjA.homEquiv _ _).symm
    ((SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E Y)).map
      (F.adjR.unit.app M) ≫ F.image.constantSquare.ordinary.hom.app (F.ordinaryR.obj M))

/-- The derived scalar unit, defined by adjunction from the same canonical kappa.
Its representative formula is asserted below, so it cannot be an arbitrary map.
Source: node proof steps 5 and 8
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.tau {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y} {f : X ⟶ Y}
    (F : Arrow l E SX SY f) (H : DR l E Y) :
    F.a.left.obj (SY.U.functor.obj H) ⟶ SX.U.functor.obj (F.r.left.obj H) :=
  (F.a.adj.homEquiv _ _).symm
    (SY.U.functor.map (F.r.adj.unit.app H) ≫ (F.kappa l E).hom.app (F.r.left.obj H))

/-- The completed R-pullback in the complete full subcategories.
Source: Stacks 099K and node proof step 9
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.leftR {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y} {f : X ⟶ Y}
    (F : Arrow l E SX SY f) :
    (completeR l E Y).FullSubcategory ⥤ (completeR l E X).FullSubcategory :=
  (completeR l E Y).ι ⋙ (completeR l E X).lift
    (F.r.left ⋙ IntegralOnSlice.completion l E X none) (fun K ↦ SX.r_output (F.r.left.obj K))

/-- The completed constant-coefficient pullback C^A f⁻¹.
Source: Stacks 099K and node proof step 9
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.leftA {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y} {f : X ⟶ Y}
    (F : Arrow l E SX SY f) :
    (SY.completeA l E).FullSubcategory ⥤ (SX.completeA l E).FullSubcategory :=
  (SY.completeA l E).ι ⋙ (SX.completeA l E).lift
    (F.a.left ⋙ SX.completion.completion) (fun K ↦ SX.a_output (F.a.left.obj K))

/-- Restrict the R direct image to complete objects, using its preservation assertion.
Source: Stacks 099K (blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.rightR {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y} {f : X ⟶ Y}
    (F : Arrow l E SX SY f)
    (h : ∀ K : DR l E X, completeR l E X K → completeR l E Y (F.r.right.obj K)) :
    (completeR l E X).FullSubcategory ⥤ (completeR l E Y).FullSubcategory :=
  (completeR l E Y).lift ((completeR l E X).ι ⋙ F.r.right)
    (fun K ↦ h K.obj K.property)

/-- Restrict the constant direct image to complete objects.
Source: Stacks 099K (blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.rightA {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y} {f : X ⟶ Y}
    (F : Arrow l E SX SY f)
    (h : ∀ K : DA l E X, SX.completeA l E K → SY.completeA l E (F.a.right.obj K)) :
    (SX.completeA l E).FullSubcategory ⥤ (SY.completeA l E).FullSubcategory :=
  (SY.completeA l E).lift ((SX.completeA l E).ι ⋙ F.a.right)
    (fun K ↦ h K.obj K.property)

/-- The completed adjunctions and their specified comparison. Hom formulas fix the
adjunctions by the reflector bijections even when eta on ordinary pullback is not
invertible. Counit, inverse-Hom and unit transport refer to these exact adjunctions.
Source: Stacks 099K; node proof steps 5 and 8--11
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
structure AdjunctionTransport {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y}
    {f : X ⟶ Y} (F : Arrow l E SX SY f) where
  r_preserves : ∀ K : DR l E X, completeR l E X K → completeR l E Y (F.r.right.obj K)
  a_preserves : ∀ K : DA l E X, SX.completeA l E K → SY.completeA l E (F.a.right.obj K)
  r : F.leftR l E ⊣ F.rightR l E r_preserves
  a : F.leftA l E ⊣ F.rightA l E a_preserves
  r_hom : ∀ (H : (completeR l E Y).FullSubcategory)
    (M : (completeR l E X).FullSubcategory) (s : (F.leftR l E).obj H ⟶ M),
    (r.homEquiv H M s).hom = F.r.adj.homEquiv H.obj M.obj
      ((IntegralOnSlice.completionUnit l E X none).app (F.r.left.obj H.obj) ≫ s.hom)
  a_hom : ∀ (H : (SY.completeA l E).FullSubcategory)
    (M : (SX.completeA l E).FullSubcategory) (s : (F.leftA l E).obj H ⟶ M),
    (a.homEquiv H M s).hom = F.a.adj.homEquiv H.obj M.obj
      (SX.completion.unit.app (F.a.left.obj H.obj) ≫ s.hom)
  r_counit : ∀ M : (completeR l E X).FullSubcategory,
    (IntegralOnSlice.completionUnit l E X none).app (F.r.left.obj (F.r.right.obj M.obj)) ≫
      (r.counit.app M).hom = F.r.adj.counit.app M.obj
  a_counit : ∀ M : (SX.completeA l E).FullSubcategory,
    SX.completion.unit.app (F.a.left.obj (F.a.right.obj M.obj)) ≫
      (a.counit.app M).hom = F.a.adj.counit.app M.obj
  b : SY.restriction l E ⋙ F.leftA l E ≅ F.leftR l E ⋙ SX.restriction l E
  b_unit : ∀ H : (completeR l E Y).FullSubcategory,
    SX.completion.unit.app (F.a.left.obj (SY.U.functor.obj H.obj)) ≫
        (b.hom.app H).hom =
      F.tau l E H.obj ≫ SX.U.functor.map
        ((IntegralOnSlice.completionUnit l E X none).app (F.r.left.obj H.obj))
  ordinary_counit : ∀ M : DR l E X,
    F.tau l E (F.r.right.obj M) ≫ SX.U.functor.map (F.r.adj.counit.app M) =
      F.a.left.map ((F.kappa l E).hom.app M) ≫
        F.a.adj.counit.app (SX.U.functor.obj M)
  counit : ∀ M : (completeR l E X).FullSubcategory,
    (b.hom.app ((F.rightR l E r_preserves).obj M)).hom ≫
        SX.U.functor.map (r.counit.app M).hom =
      (F.a.left ⋙ SX.completion.completion).map ((F.kappa l E).hom.app M.obj) ≫
        (a.counit.app ((SX.restriction l E).obj M)).hom
  hom : ∀ (H : (completeR l E Y).FullSubcategory)
    (M : (completeR l E X).FullSubcategory)
    (s : H ⟶ (F.rightR l E r_preserves).obj M),
    (b.hom.app H).hom ≫ SX.U.functor.map ((r.homEquiv H M).symm s).hom =
      ((a.homEquiv ((SY.restriction l E).obj H) ((SX.restriction l E).obj M)).symm
        (ObjectProperty.homMk
          (SY.U.functor.map s.hom ≫ (F.kappa l E).hom.app M.obj))).hom
  unit : ∀ H : (completeR l E Y).FullSubcategory,
    SY.U.functor.map (r.unit.app H).hom ≫
        (F.kappa l E).hom.app ((F.leftR l E).obj H).obj ≫
        F.a.right.map (b.inv.app H).hom = (a.unit.app ((SY.restriction l E).obj H)).hom

/-- The normalization of completion of ordinary pullback against the *specified*
quotient-tower pullback. The chain augmentation has product component given by all
finite mates and zero shifted-product component. It determines the comparison on
all flat-term K-flat representatives without any boundedness hypothesis.
Source: node proof step 5
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.PullbackNormalization {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y}
    {f : X ⟶ Y} (F : Arrow l E SX SY f) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
    ∃ (q : ∀ n : ℕ, (F.ordinaryR.mapHomologicalComplex (.up ℤ)).obj P.obj ⟶
        (integralOperationsPullbackLevel l E f n).obj P.obj)
      (α : (F.ordinaryR.mapHomologicalComplex (.up ℤ)).obj P.obj ⟶
        (integralOperationsPullbackComplexFunctor l E f).obj P.obj),
      (∀ (n : ℕ) (i : ℤ) (V : Y.ProEt) (x : (P.obj.X i).val.obj (op V)),
        HEq ((((F.adjR.mapHomologicalComplex (.up ℤ)).homEquiv _ _ (q n)).f i).val.app
          (op V) x)
          (integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X i) V
            (unrestrictedIntegralTensorSection l E Y n (P.obj.X i) (op V) 1 x))) ∧
      (α ≫ CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ (integralOperationsPullbackLevel l E f n).obj P.obj)
          (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj
            P.obj))) = Pi.lift q) ∧
      (∀ (i j : ℤ) (h : i + -1 = j),
        α.f i ≫ (CochainComplex.mappingCocone.snd
          (towerTransitionEndomorphism
            (K := fun n : ℕ ↦ (integralOperationsPullbackLevel l E f n).obj P.obj)
            (integralOperationsTowerStep
              ((integralOperationsPullbackTowerFunctor l E f).obj P.obj)))).v i j h = 0) ∧
      (IntegralOnSlice.completionUnit l E X none).app (F.r.left.obj (DerivedCategory.Q.obj
          P.obj)) ≫ F.pullback.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (integralDerivedPullbackComparison l E f).hom.app P =
        F.r.epsilon.app P.obj ≫ DerivedCategory.Q.map α

/-- The ordinary scalar-unit comparison on complexes, using the same two ordinary
adjunctions and the same sectionwise coefficient square in every degree.
Source: Stacks 03D7 and 07A6
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.scalarComplex {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y}
    {f : X ⟶ Y} (F : Arrow l E SX SY f)
    (P : CochainComplex (CompletedCoefficientPushforward.Mod Y
      (completedIntegralCoefficientSheafUnrestricted l E Y)) ℤ) :
    (F.ordinaryA.mapHomologicalComplex (.up ℤ)).obj ((restrictionComplex l E Y).obj P) ⟶
      (restrictionComplex l E X).obj ((F.ordinaryR.mapHomologicalComplex (.up ℤ)).obj P) :=
  ((F.adjA.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
    ((restrictionComplex l E Y).map ((F.adjR.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      (NatIso.mapHomologicalComplex F.image.constantSquare.ordinary (.up ℤ)).hom.app
        ((F.ordinaryR.mapHomologicalComplex (.up ℤ)).obj P))

/-- The derived scalar-unit comparison computes the ordinary scalar unit on every
good representative. This is the normalization in the ringed counit dependency.
Source: Stacks 03D7, 07A6 and 0D6E; node proof step 8
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
def Arrow.TauNormalization {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y}
    {f : X ⟶ Y} (F : Arrow l E SX SY f) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
    F.tau l E (DerivedCategory.Q.obj P.obj) ≫ SX.U.functor.map (F.r.epsilon.app P.obj) ≫
        SX.U.factors.hom.app ((F.ordinaryR.mapHomologicalComplex (.up ℤ)).obj P.obj) =
      F.a.left.map (SY.U.factors.hom.app P.obj) ≫
        F.a.epsilon.app ((restrictionComplex l E Y).obj P.obj) ≫
          DerivedCategory.Q.map (F.scalarComplex l E P.obj)

/-- A ringed pullback tensorator, normalized by the tensor of its ordinary adjunction
units on homogeneous generators. This is the sheafified tensor reassociation map of
Stacks 07A4, expressed without choosing a presentation of the ordinary left adjoint.
Source: node proof steps 2 and 7
(blueprint: def-pur-completed-coefficient-adjunction-transport-models). -/
structure PullTensor {X Y : Scheme.{t}} (f : X ⟶ Y)
    (RX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)})
    (RY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (c : (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY ⟶
      (CompletedCoefficientPushforward.ringPush.{t, u} f).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RX))
    (L : CompletedCoefficientPushforward.Mod Y
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY) ⥤
      CompletedCoefficientPushforward.Mod X
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RX)) [L.Additive]
    [(CompletedCoefficientPushforward.push.{t, u} f c).Additive]
    (adj : L ⊣ CompletedCoefficientPushforward.push.{t, u} f c)
    (p : CategoryTheory.RingedCoefficientCounit.DerivedAdjunction.{(max u (t + 1)) + 1,
        (max u (t + 1)) + 1, max u (t + 1), (max u (t + 1)) + 1, max u (t + 1)} L
      (CompletedCoefficientPushforward.push.{t, u} f c) adj)
    (MX : RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
      (Scheme.ProEt.topology X) RX)
    (MY : RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
      (Scheme.ProEt.topology Y) RY) where
  monoidal : letI := MY.closed.monoidal; letI := MX.closed.monoidal
    p.left.Monoidal
  representatives : letI := MY.closed.monoidal; letI := MX.closed.monoidal
    letI := monoidal
    ∀ P Q : CochainComplex (CompletedCoefficientPushforward.Mod Y
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY)) ℤ,
    ∀ (hP : CochainComplex.IsKFlatIndependentCoefficients (R := RY) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := RY) Q),
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (J := Scheme.ProEt.topology Y) (R := RY) (P.X n)) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (J := Scheme.ProEt.topology Y) (R := RY) (Q.X n)) →
    ∃ (hLP : CochainComplex.IsKFlatIndependentCoefficients (R := RX)
        ((L.mapHomologicalComplex (.up ℤ)).obj P))
      (hLQ : CochainComplex.IsKFlatIndependentCoefficients (R := RX)
        ((L.mapHomologicalComplex (.up ℤ)).obj Q))
      (χ : (L.mapHomologicalComplex (.up ℤ)).obj ((total.{t, u} Y RY).obj (P, Q)) ⟶
        (total.{t, u} X RX).obj ((L.mapHomologicalComplex (.up ℤ)).obj P,
          (L.mapHomologicalComplex (.up ℤ)).obj Q)),
      (∀ (i j k : ℤ) (h : i + j = k) (V : Y.ProEtᵒᵖ)
        (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
        HEq ((((adj.mapHomologicalComplex (.up ℤ)).homEquiv _ _ χ).f k).val.app V
          (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology Y) RY
            P Q i j k h V x y))
          (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology X) RX
            ((L.mapHomologicalComplex (.up ℤ)).obj P)
            ((L.mapHomologicalComplex (.up ℤ)).obj Q) i j k h
            ((Scheme.proEtaleBaseChange f).op.obj V)
            ((((adj.mapHomologicalComplex (.up ℤ)).unit.app P).f i).val.app V x)
            ((((adj.mapHomologicalComplex (.up ℤ)).unit.app Q).f j).val.app V y))) ∧
      p.left.map ((MY.models.iso _ _ _ P Q hP hQ).inv) ≫
          p.epsilon.app ((total.{t, u} Y RY).obj (P, Q)) ≫ DerivedCategory.Q.map χ =
        (Functor.Monoidal.μIso p.left (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj Q)).inv ≫
          MX.closed.tensor.map (Prod.mkHom (p.epsilon.app P) (p.epsilon.app Q)) ≫
            (MX.models.iso _ _ _ _ _ hLP hLQ).inv

end WeilConjectures.CompletedCoefficientTransport
