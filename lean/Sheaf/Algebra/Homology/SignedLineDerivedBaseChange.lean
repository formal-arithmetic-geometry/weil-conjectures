/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.SignedLineScalarPullbackSquare
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Sites.Pullback

import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.CategoryTheory.Sites.LocalProperties
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback
import Sheaf.SecSmoothPurity.CochainInverseComparison
import Sheaf.Paper.ScalarExtensionBinaryCoherence
import Sheaf.Paper.InvertibleTensorScalarExtension
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

public import Sheaf.CategoryTheory.RingedToposMorphism

public import Sheaf.CategoryTheory.RingedSiteModules

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Signed line comparisons on unbounded derived categories

Source: Stacks Project, Tags 03EL, 0GMX, 0FNY and 07A4; blueprint main-20261015,
Powers and duals in det-prop-sfb-cartesian-coefficients-twists.
(blueprint: lem-pur-signed-line-derived-base-change)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w z

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace SheafOfModules.SignedLineDerivedBaseChange

attribute [local irreducible] siteDerivedTensorIndependentCoefficients
  KFlatFixedTensor.representativeIso siteSheafTensorRight
  siteSheafTensorSecondMap siteSheafTensorTmul

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

/-- The existing module pullback; its unit is insertion into the sheafified relative tensor.
Source: Stacks 03D7 and 03EL (blueprint: lem-pur-signed-line-derived-base-change). -/
abbrev pull
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) :=
  ringedSitePullbackFunctor a (module_pushforward_isRightAdjoint_of_universes a)

/-- Signed functoriality in a line isomorphism, using the recorded powers and internal Hom.
The negative map is precomposition with the inverse positive map.
Source: Stacks 03EL, 0GMX (blueprint: lem-pur-signed-line-derived-base-change). -/
def signedIsoHom {A : Sheaf J CommRingCat.{max u v w}}
    {P Q : KFlatFixedTensor.Modules A} (b : P ≅ Q) :
    ∀ d : ℤ, signedLinePower.{u, v, w} P d ⟶ signedLinePower.{u, v, w} Q d
  | .ofNat n => scalarTensorPowerMap A b.hom n
  | .negSucc n => homObjMap (scalarTensorPowerMap A b.inv (n + 1)) (𝟙 (unit _))

/-- The published derived tensor with the line in degree zero.
Source: Stacks 06YU (blueprint: lem-pur-signed-line-derived-base-change). -/
def derivedLine (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (L : KFlatFixedTensor.Modules A) :
    DerivedCategory (KFlatFixedTensor.Modules A) ⥤ DerivedCategory (KFlatFixedTensor.Modules A) :=
  (KFlatFixedTensor.derivedTensor A).flip.obj
    (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L))

attribute [local irreducible] derivedLine Functor.mapDerivedCategory

/-- The actual total-complex collapse, followed by the existing comparison with site tensor.
Source: Stacks 06YU (blueprint: lem-pur-signed-line-derived-base-change). -/
def collapse (A : Sheaf J CommRingCat.{max u v w})
    (L : KFlatFixedTensor.Modules A) :
    (KFlatFixedTensor.totalTensor A).flip.obj
        ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L) ≅
      (siteSheafTensorRight (A := A) L).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (KFlatFixedTensor.ordinaryTensor A) L ≪≫
    NatIso.mapHomologicalComplex ((siteSheafTensorRightIso A L).symm) (.up ℤ)

/-- Agreement with the actual K-flat total-tensor comparison on resolving complexes.
Source: Stacks 06YU (blueprint: lem-pur-signed-line-derived-base-change). -/
def ResolvingNormalization (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (L : KFlatFixedTensor.Modules A)
    (hL : CochainComplex.IsKFlatIndependentCoefficients
      ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L))
    (hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := A)
      (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L).X i))
    (c : DerivedCategory.Q ⋙ derivedLine A L ≅
      (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) : Prop :=
  ∀ (E : CochainComplex (KFlatFixedTensor.Modules A) ℤ)
    (hE : CochainComplex.IsKFlatIndependentCoefficients E)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := A) (E.X i)),
    HEq (c.hom.app E ≫ DerivedCategory.Q.map ((collapse A L).inv.app E))
      (KFlatFixedTensor.representativeIso A E
        ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L)
          hE hL hf hLf).inv

/-- The two localization comparisons and the derived action isomorphism, as ordinary
product data. Their canonicity is specified by DerivedAction, never chosen from existence.
Source: Stacks 06YU, 07A4 (blueprint: lem-pur-signed-line-derived-base-change). -/
def DerivedActionData
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S) :=
  (DerivedCategory.Q ⋙ derivedLine R L ≅
    (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ×
  (DerivedCategory.Q ⋙ derivedLine S M ≅
    (siteSheafTensorRight M).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ×
  (derivedLine R L ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ derivedLine S M)

/-- A derived action pinned on every complex by the ordinary tensor comparison.
The resolving comparisons are the published ones, including their collapse to one-term
line factors. Source: Stacks 06YU, 07A4 and 015F
(blueprint: lem-pur-signed-line-derived-base-change). -/
def DerivedAction
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M)
    (b : DerivedActionData F L M) : Prop :=
  ∃ hL : CochainComplex.IsKFlatIndependentCoefficients
    ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules R) 0).obj L),
  ∃ hM : CochainComplex.IsKFlatIndependentCoefficients
    ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules S) 0).obj M),
  ∃ hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R)
    (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules R) 0).obj L).X i),
  ∃ hMf : ∀ i : ℤ, IsFlatOnSite (J := K) (R := S)
    (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules S) 0).obj M).X i),
    ResolvingNormalization R L hL hLf b.1 ∧
    ResolvingNormalization S M hM hMf b.2.1 ∧
    (∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
      HEq (b.2.2.hom.app (DerivedCategory.Q.obj E) ≫
          (derivedLine S M).map (F.mapDerivedCategoryFactors.hom.app E) ≫
          b.2.1.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E))
        (F.mapDerivedCategory.map (b.1.hom.app E) ≫
          F.mapDerivedCategoryFactors.hom.app
            (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E))) ∧
    (∀ η : derivedLine R L ⋙ F.mapDerivedCategory ≅
        F.mapDerivedCategory ⋙ derivedLine S M,
      (∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
        HEq (η.hom.app (DerivedCategory.Q.obj E) ≫
            (derivedLine S M).map (F.mapDerivedCategoryFactors.hom.app E) ≫
            b.2.1.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E))
          (F.mapDerivedCategory.map (b.1.hom.app E) ≫
            F.mapDerivedCategoryFactors.hom.app
              (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E))) →
        η = b.2.2)

/-- Right unit, positive-power associator and negative-positive evaluation constraints.
The ordinary constraints are specified on all local pure tensors. The derived constraints
are specified after localization using c; c itself is fixed by representativeIso and
collapse in DerivedAction. Thus these are the canonical constraints, with no arbitrary
monoidal structure or map selected. The positive constraint is the associator followed
by the one-term identification of the next power, and evaluation contracts the last two
factors. Source: Stacks 03EK, 04TT, 06YU and 07A4
(blueprint: lem-pur-signed-line-derived-base-change). -/
def DerivedLineConstraints (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (P : KFlatFixedTensor.Modules A)
    (c : ∀ d : ℤ, DerivedCategory.Q ⋙ derivedLine A (signedLinePower.{u, v, w} P d) ≅
      (siteSheafTensorRight (signedLinePower.{u, v, w} P d)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)
    (rightUnitor : derivedLine A (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _)
    (product : ∀ n : ℕ,
      derivedLine A (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
          derivedLine A (signedLinePower.{u, v, w} P 1) ≅
        derivedLine A (signedLinePower.{u, v, w} P (.ofNat (n + 2))))
    (evaluation : ∀ n : ℕ,
      derivedLine A (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
        derivedLine A (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _) : Prop :=
  ∃ ordinaryUnit : siteSheafTensorRight (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _,
  ∃ ordinaryProduct : ∀ n : ℕ,
    siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P 1) ≅
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 2))),
  ∃ ordinaryEvaluation : ∀ n : ℕ,
    siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _,
    (∀ (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (r : A.obj.obj V),
      (ordinaryUnit.hom.app N).val.app V
        (siteSheafTensorTmul N (signedLinePower.{u, v, w} P 0) V x r) =
          @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
            (N.val.obj V) inferInstance r x) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (y : (scalarTensorPower A P (n + 1)).val.obj V)
      (q : P.val.obj V),
      ((ordinaryProduct n).hom.app N).val.app V
        (siteSheafTensorTmul _ P V
          (siteSheafTensorTmul N (scalarTensorPower A P (n + 1)) V x y) q) =
        siteSheafTensorTmul N (scalarTensorPower A P (n + 2)) V x
          (siteSheafTensorTmul (scalarTensorPower A P (n + 1)) P V y q)) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (φ : (signedLinePower.{u, v, w} P (.negSucc n)).val.obj V)
      (y : (scalarTensorPower A P (n + 1)).val.obj V),
      ((ordinaryEvaluation n).app N).val.app V
        (siteSheafTensorTmul _ (scalarTensorPower A P (n + 1)) V
          (siteSheafTensorTmul N (signedLinePower.{u, v, w} P (.negSucc n)) V x φ) y) =
        @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
          (N.val.obj V) inferInstance (φ.app (op (Over.mk (𝟙 V.unop))) y) x) ∧
    (∀ E : CochainComplex (KFlatFixedTensor.Modules A) ℤ,
      HEq (rightUnitor.hom.app (DerivedCategory.Q.obj E))
        ((c 0).hom.app E ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinaryUnit (.up ℤ)).hom.app E))) ∧
    (∀ (n : ℕ) (E : CochainComplex (KFlatFixedTensor.Modules A) ℤ),
      HEq ((product n).hom.app (DerivedCategory.Q.obj E) ≫
          (c (.ofNat (n + 2))).hom.app E)
        ((derivedLine A (signedLinePower.{u, v, w} P 1)).map
            ((c (.ofNat (n + 1))).hom.app E) ≫
          (c 1).hom.app
            ((Functor.mapHomologicalComplex
              (siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))))
                (.up ℤ)).obj E) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (ordinaryProduct n) (.up ℤ)).hom.app E))) ∧
    (∀ (n : ℕ) (E : CochainComplex (KFlatFixedTensor.Modules A) ℤ),
      HEq ((evaluation n).app (DerivedCategory.Q.obj E))
        ((derivedLine A (signedLinePower.{u, v, w} P (.ofNat (n + 1)))).map
            ((c (.negSucc n)).hom.app E) ≫
          (c (.ofNat (n + 1))).hom.app
            ((Functor.mapHomologicalComplex
              (siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n)))
                (.up ℤ)).obj E) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (ordinaryEvaluation n) (.up ℤ)).app E)))

/-- The simultaneous unit, positive-power and evaluation equations for the same eta family
whose components are fixed in DerivedAction. Source: Stacks 07A4; blueprint Powers and duals
(blueprint: lem-pur-signed-line-derived-base-change). -/
def DerivedFamilyCoherence
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
    (b : ∀ d : ℤ, DerivedActionData F (signedLinePower.{u, v, w} P d)
      (signedLinePower.{u, v, w} Q d)) : Prop :=
  ∃ unitR : derivedLine R (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _,
  ∃ unitS : derivedLine S (signedLinePower.{u, v, w} Q 0) ≅ 𝟭 _,
  ∃ productR : ∀ n : ℕ,
    derivedLine R (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
        derivedLine R (signedLinePower.{u, v, w} P 1) ≅
      derivedLine R (signedLinePower.{u, v, w} P (.ofNat (n + 2))),
  ∃ productS : ∀ n : ℕ,
    derivedLine S (signedLinePower.{u, v, w} Q (.ofNat (n + 1))) ⋙
        derivedLine S (signedLinePower.{u, v, w} Q 1) ≅
      derivedLine S (signedLinePower.{u, v, w} Q (.ofNat (n + 2))),
  ∃ evaluationR : ∀ n : ℕ,
    derivedLine R (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
      derivedLine R (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _,
  ∃ evaluationS : ∀ n : ℕ,
    derivedLine S (signedLinePower.{u, v, w} Q (.negSucc n)) ⋙
      derivedLine S (signedLinePower.{u, v, w} Q (.ofNat (n + 1))) ⟶ 𝟭 _,
    DerivedLineConstraints R P (fun d ↦ (b d).1) unitR productR evaluationR ∧
    DerivedLineConstraints S Q (fun d ↦ (b d).2.1) unitS productS evaluationS ∧
    (∀ X : DerivedCategory (KFlatFixedTensor.Modules R),
      (b 0).2.2.hom.app X ≫ unitS.hom.app (F.mapDerivedCategory.obj X) =
        F.mapDerivedCategory.map (unitR.hom.app X)) ∧
    (∀ (n : ℕ) (X : DerivedCategory (KFlatFixedTensor.Modules R)),
      F.mapDerivedCategory.map ((productR n).hom.app X) ≫
          (b (.ofNat (n + 2))).2.2.hom.app X =
        (b 1).2.2.hom.app ((derivedLine R
            (signedLinePower.{u, v, w} P (.ofNat (n + 1)))).obj X) ≫
          (derivedLine S (signedLinePower.{u, v, w} Q 1)).map
            ((b (.ofNat (n + 1))).2.2.hom.app X) ≫
          (productS n).hom.app (F.mapDerivedCategory.obj X)) ∧
    (∀ (n : ℕ) (X : DerivedCategory (KFlatFixedTensor.Modules R)),
      F.mapDerivedCategory.map ((evaluationR n).app X) =
        (b (.ofNat (n + 1))).2.2.hom.app
            ((derivedLine R (signedLinePower.{u, v, w} P (.negSucc n))).obj X) ≫
          (derivedLine S (signedLinePower.{u, v, w} Q (.ofNat (n + 1)))).map
            ((b (.negSucc n)).2.2.hom.app X) ≫
          (evaluationS n).app (F.mapDerivedCategory.obj X))

variable
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
  (t : (pull a).obj P ≅ Q)

/-- Naturality in isomorphisms of the two line data. Negative powers use inverse dual maps.
Source: Stacks 03EL, 0GMX (blueprint: lem-pur-signed-line-derived-base-change). -/
def IsoNaturality
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d) : Prop :=
  ∀ (P' : KFlatFixedTensor.Modules R) (Q' : KFlatFixedTensor.Modules S)
    (b : P ≅ P') (c : Q ≅ Q') (t' : (pull a).obj P' ≅ Q')
    (T' : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P' d) ≅
      signedLinePower.{u, v, w} Q' d),
    (pull a).map b.hom ≫ t'.hom = t.hom ≫ c.hom →
    SignedLinePullbackNormalized a P' Q' t' T' →
    ∀ d : ℤ, (pull a).map (signedIsoHom b d) ≫ (T' d).hom =
      (T d).hom ≫ signedIsoHom c d

/-- Naturality in arbitrary coefficient extensions compatible with the structural isomorphism.
The existing scalar-power identifications and scalar/pullback square specify the canonical
balanced-tensor comparison; no arbitrary comparison is assumed. Degree-one compatibility
is exactly the assertion that t' is induced from t. No flatness of either ring map occurs.
Source: Stacks 03EL, 0GMX, 0FNY
(blueprint: lem-pur-signed-line-derived-base-change). -/
def ScalarNaturality
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d) : Prop :=
  ∀ (R' : Sheaf J CommRingCat.{max u v w})
    (S' : Sheaf K CommRingCat.{max u v w}) (α : R ⟶ R') (β : S ⟶ S')
    (a' : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R' ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S')),
    IsIso ((rAdj.homEquiv _ _).symm a') →
    (sheafCompose J (forget₂ CommRingCat RingCat)).map α ≫ a' =
      a ≫ (U.sheafPushforwardContinuous RingCat J K).map
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map β) →
    ∀ (t' : (pull a').obj (changeOfRingsOfUniverses α P) ≅ changeOfRingsOfUniverses β Q)
      (T' : ∀ d : ℤ,
        (pull a').obj (signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d) ≅
          signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d)
      (B : ∀ d : ℤ, changeOfRingsOfUniverses α (signedLinePower.{u, v, w} P d) ≅
        signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d)
      (E : ∀ d : ℤ, changeOfRingsOfUniverses β (signedLinePower.{u, v, w} Q d) ≅
        signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d),
      SignedLinePullbackNormalized a' _ _ t' T' →
      SignedLineComparisonNormalized α P _ (Iso.refl _) B →
      SignedLineComparisonNormalized β Q _ (Iso.refl _) E →
      SignedLineScalarPullbackSquare α β a a' P _ Q _
        (Iso.refl _) (Iso.refl _) t t' →
      ∀ d : ℤ, SignedLineScalarPullbackSquare α β a a'
        (signedLinePower.{u, v, w} P d)
        (signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d)
        (signedLinePower.{u, v, w} Q d)
        (signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d)
        (B d) (E d) (T d) (T' d)

/-- The unique normalized signed comparisons, their naturality, and their canonical
unbounded derived tensor action.
Source: Stacks 03EL, 0GMX, 0FNY, 06YQ, 07A4 and 015F; blueprint Powers and duals
(blueprint: lem-pur-signed-line-derived-base-change).

Proof:
1. The structural ring isomorphism identifies relative tensor pullback with the
exact abelian inverse image. Its unit multiplies coefficient factors.
2. Restrict to a trivializing cover. Tensor powers and internal duals have their
usual tensor and dual bases. Evaluation is multiplication, so it is invertible;
these evaluations and their inverses glue independently of the chosen basis.
3. Start with the coefficient unit and t. Iterate the canonical tensor comparison,
with the fixed associators, to obtain all positive maps uniquely.
4. Apply finite_free_dual_pullback to each positive power; precompose functionals
with the inverse positive comparison. The evaluation equation characterizes the
negative map uniquely and carries a pulled dual basis to the corresponding dual basis.
5. Tensor recursion and contravariant naturality of the dual comparison prove
naturality in line isomorphisms; evaluation uniqueness handles negative degrees.
6. Reassociate scalar extension across the compatible coefficient square. On pure
sections the comparison multiplies the two scalar factors, and its inverse inserts 1.
It preserves tensor and unit, proving positive scalar naturality by induction.
7. Scalar extension preserves the dual-basis evaluation formula. Both negative maps
satisfy the same evaluation equation, so uniqueness identifies them, without flatness.
8. Exact termwise pullback preserves quasi-isomorphisms. The exact-functor
localization theorem supplies D(F) and identifies it with the total left derived functor.
9. Tensoring by a line is an equivalence, with inverse its dual, hence exact. The
one-term line complexes are therefore flat-term K-flat complexes (06YQ).
10. Apply unbounded derived tensor pullback (07A4), then tensor with t_d in degree
zero. Bifunctoriality gives naturality in every morphism of the unbounded input.
11. The derived monoidal unit and associator diagrams, computed on K-flat flat-term
representatives, restrict on one-term lines to the ordinary normalized comparisons.
The resolving comparison and degree-zero collapse give ResolvingNormalization.
The final localization square is the termwise tensor comparison on every complex;
therefore it preserves the unit, tensor-power recursion and evaluation equalities.
No boundedness assumption on the varying complex has entered the argument. -/
theorem signed_line_derived_base_change
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (_ha : IsIso ((rAdj.homEquiv _ _).symm a))
    (_hP : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (P.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i))))
    (_hQ : ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
      ∀ i : I, Nonempty (Q.over (V i) ≅
        unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (V i))))
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)] :
    ∃ (hAdd : (pull a).Additive)
      (hLim : PreservesFiniteLimits (pull a)) (hCol : PreservesFiniteColimits (pull a)),
    ∃! T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
        signedLinePower.{u, v, w} Q d,
      SignedLinePullbackNormalized a P Q t T ∧
      (∀ T', SignedLinePullbackNormalized a P Q t T' → T' = T) ∧
      IsoNaturality a P Q t T ∧ ScalarNaturality a P Q t rInv rAdj T ∧
      (fun [_add : (pull a).Additive] [_lim : PreservesFiniteLimits (pull a)]
        [_col : PreservesFiniteColimits (pull a)] ↦
        ∃ γ : ∀ d : ℤ, siteSheafTensorRight (signedLinePower.{u, v, w} P d) ⋙ pull a ≅
            pull a ⋙ siteSheafTensorRight (signedLinePower.{u, v, w} Q d),
          (∀ (d : ℤ) (M : KFlatFixedTensor.Modules R) (V : C) (x : M.val.obj (op V))
            (y : (signedLinePower.{u, v, w} P d).val.obj (op V)),
            ((γ d).hom.app M).val.app (op (U.obj V))
                (ringedSitePullbackSection a
                  (module_pushforward_isRightAdjoint_of_universes a)
                  ((siteSheafTensorRight (signedLinePower.{u, v, w} P d)).obj M) V
                  (siteSheafTensorTmul M (signedLinePower.{u, v, w} P d) (op V) x y)) =
              siteSheafTensorTmul ((pull a).obj M) (signedLinePower.{u, v, w} Q d)
                (op (U.obj V))
                (ringedSitePullbackSection a
                  (module_pushforward_isRightAdjoint_of_universes a) M V x)
                ((T d).hom.val.app (op (U.obj V))
                  (ringedSitePullbackSection a
                    (module_pushforward_isRightAdjoint_of_universes a)
                    (signedLinePower.{u, v, w} P d) V y))) ∧
          ∃ b : ∀ d : ℤ, DerivedActionData (pull a) (signedLinePower.{u, v, w} P d)
            (signedLinePower.{u, v, w} Q d),
            (∀ d : ℤ, DerivedAction (pull a) (signedLinePower.{u, v, w} P d)
              (signedLinePower.{u, v, w} Q d) (γ d) (b d)) ∧
            DerivedFamilyCoherence (pull a) P Q b)
        (_add := hAdd) (_lim := hLim) (_col := hCol) := by
  sorry

end SheafOfModules.SignedLineDerivedBaseChange
