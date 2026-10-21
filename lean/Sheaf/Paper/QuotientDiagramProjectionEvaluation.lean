/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.Paper.SemilinearDerivedCalculus
public import Sheaf.Paper.SemilinearGeometryCore
public import Sheaf.Paper.SemilinearGeometryDerived
public import Sheaf.Paper.SemilinearGeometryOps
import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.SystemRingedSequenceSite
import Sheaf.CategoryTheory.SystemLevelLeftExtension
import Sheaf.CategoryTheory.SystemEvaluationTopos
import Sheaf.CategoryTheory.SystemSingleDerivedExtension
import Sheaf.CategoryTheory.SystemOrdinarySingleExtension
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.CategoryTheory.SystemSingleDerivedEvaluation

/-! # Evaluation of the quotient-diagram projection mate

Source: Stacks, sites-cohomology.tex, Tags 0B56 (equation-projection-formula-map),
07A4 (lemma-pullback-tensor-product), 07A6 (lemma-adjoint); Zheng, Construction 4.1.
(blueprint: lem-pur-quotient-diagram-projection-evaluation).

The presentation records below specify ordinary functors on the actual sequence site
before deriving them. Their section and representative equations fix the canonical
maps; the existence theorem imposes no condition on the derived inputs. Level `n`
means the positive exponent `n+1`.

The main definitions are `Reduction`, `TensorReduction`, `Presentation`,
`coefficientMate`, `arrow`, and `Laws`. The main statement is
`quotientDiagramProjectionEvaluation`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open WeilConjectures.SemilinearSections

namespace SheafOfModules.QuotientDiagramProjection

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} X]

/-- Sheafification on the chosen small model, using the existing site equivalence theorem.
Source: Mathlib Sites.Equivalence
(blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
instance ringSheafify (J : GrothendieckTopology C) :
    HasSheafify J CommRingCat.{max c v r} := hasSheafifyEssentiallySmallSite.{v, max c v r, c,
      (max c v r) + 1, max c v r} J CommRingCat.{max c v r}

/-- The existing constant-sheaf functor in the module universe.
Source: Stacks 03H2 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
abbrev constant (J : GrothendieckTopology C) (A : Type (max c v r)) [CommRing A] :=
  (@constantSheaf C _ J CommRingCat.{max c v r} _
    (@HasSheafify.isRightAdjoint C _ J CommRingCat.{max c v r} _
      (ringSheafify.{c, v, r} J))).obj (CommRingCat.of A)

/-- The actual positive quotient coefficient sheaf.
Source: Stacks 0B56 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
abbrev finite (J : GrothendieckTopology C) (A : Type (max c v r)) [CommRing A]
    (I : Ideal A) (n : ℕ) := constant.{c, v, r} J (A ⧸ I ^ (n + 1))

/-- The quotient augmentation, using the actual ring quotient map.
Source: Stacks 0B56 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
def quotientMap (J : GrothendieckTopology C) (A : Type (max c v r)) [CommRing A]
    (I : Ideal A) (n : ℕ) : constant.{c, v, r} J A ⟶ finite.{c, v, r} J A I n :=
  (@constantSheaf C _ J CommRingCat.{max c v r} _
    (@HasSheafify.isRightAdjoint C _ J CommRingCat.{max c v r} _
      (ringSheafify.{c, v, r} J))).map
    (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The genuine successive quotient transition; index zero means exponent one.
Source: Stacks 0B56 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
def quotientTransition (J : GrothendieckTopology C) (A : Type (max c v r)) [CommRing A]
    (I : Ideal A) (n : ℕ) : finite.{c, v, r} J A I (n + 1) ⟶ finite.{c, v, r} J A I n :=
  (@constantSheaf C _ J CommRingCat.{max c v r} _
    (@HasSheafify.isRightAdjoint C _ J CommRingCat.{max c v r} _
      (ringSheafify.{c, v, r} J))).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))

/-- A presentation of `S Delta`, fixed by ordinary scalar insertion, every transition,
and its universal K-flat computation. No derived diagram category is substituted for
this ordinary localization. Source: Stacks 06YY; Zheng 4.1
(blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
structure Reduction (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max c v r})
    (B : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (q : ∀ n : ℕ, R ⟶ B n) where
  levels : ∀ n : ℕ, SemilinearSections.ScalarData.{c, v, max c v r} (q n)
  ordinary : SemilinearSections.Mod.{c, v, max c v r} J R ⥤ SemilinearSections.Systems.{c, v, max
      c v r} J B τ
  [additive : ordinary.Additive]
  ordinaryEvaluation : ∀ n : ℕ,
    ordinary ⋙ SemilinearSections.evaluation.{c, v, max c v r} J B τ n ≅ (levels n).model.E
  transition_unit : ∀ {m n : ℕ} (h : n ≤ m) (M : SemilinearSections.Mod.{c, v, max c v r} J R)
    (U : Cᵒᵖ) (x : M.val.obj U),
    HEq
      (((ordinaryEvaluation n).hom.app M).val.app U
        (((SemilinearSections.transition.{c, v, max c v r} J B τ h).app (ordinary.obj M)).val.app U
          (((ordinaryEvaluation m).inv.app M).val.app U
            (((levels m).ordinaryAdjunction.unit.app M).val.app U x))))
      (((levels n).ordinaryAdjunction.unit.app M).val.app U x)
  functor : SemilinearSections.D.{c, v, max c v r} J R ⥤ SemilinearSections.DS.{c, v, max c v r} J
      B τ
  epsilon : DerivedCategory.Q ⋙ functor ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : functor.IsLeftDerivedFunctor epsilon
    (HomologicalComplex.quasiIso (SemilinearSections.Mod.{c, v, max c v r} J R) (.up ℤ))
  computes : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P → IsIso (epsilon.app P)
  ordinaryComplexEvaluation : ∀ n : ℕ,
    ordinary.mapHomologicalComplex (.up ℤ) ⋙
        (SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ) ≅
      (levels n).model.E.mapHomologicalComplex (.up ℤ)
  ordinaryComplexEvaluation_component : ∀ (n : ℕ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) (i : ℤ),
    ((ordinaryComplexEvaluation n).hom.app P).f i =
      (ordinaryEvaluation n).hom.app (P.X i)
  evaluation : ∀ n : ℕ, functor ⋙ SemilinearSections.e.{c, v, max c v r} J B τ n ≅ (levels n).T
  evaluation_model : ∀ (n : ℕ) (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R)
      ℤ),
    (evaluation n).hom.app (DerivedCategory.Q.obj P) ≫ (levels n).model.ε.app P =
      (SemilinearSections.e.{c, v, max c v r} J B τ n).map (epsilon.app P) ≫
        (Functor.mapDerivedCategoryFactors
          (SemilinearSections.evaluation.{c, v, max c v r} J B τ n)).hom.app
            ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((ordinaryComplexEvaluation n).hom.app P)

attribute [instance] Reduction.additive

/-- The ordinary quotient augmentation, using the normalized scalar adjunction unit.
Source: Stacks 07A6 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
def Reduction.insertion {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {B : ℕ → Sheaf J CommRingCat.{max c v r}} {τ : ∀ n : ℕ, B (n + 1) ⟶ B n}
    {q : ∀ n : ℕ, R ⟶ B n} (s : Reduction.{c, v, r} J R B τ q) (n : ℕ) (M :
      SemilinearSections.Mod.{c, v, max c v r} J R) :
    (SemilinearSections.underlying.{c, v, r} J R).obj M ⟶
      (SemilinearSections.underlying.{c, v, r} J (B n)).obj ((SemilinearSections.evaluation.{c, v,
      max c v r} J B τ n).obj (s.ordinary.obj M)) :=
  (SemilinearSections.underlying.{c, v, r} J R).map ((s.levels n).ordinaryAdjunction.unit.app M) ≫
    (SemilinearSections.underlying.{c, v, r} J (B n)).map ((s.ordinaryEvaluation n).inv.app M)

/-- Canonical tensor balancing for a reduction presentation, on whole-system K-flat
representatives. Its ordinary comparison is fixed by the level scalar comparisons,
which themselves carry the pure-tensor normalization. Source: Stacks 07A4, 06YY
(blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
structure TensorReduction {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {B : ℕ → Sheaf J CommRingCat.{max c v r}} {τ : ∀ n : ℕ, B (n + 1) ⟶ B n}
    {q : ∀ n : ℕ, R ⟶ B n} (s : Reduction.{c, v, r} J R B τ q) (a : SemilinearSections.Data.{c, v,
      r} J B τ) where
  ambient : SemilinearSections.Closed.{c, v, r} J R
  ambientModels : SemilinearSections.Models.{c, v, r} J R ambient
  balance : ambient.tensor ⋙ s.functor ≅ (s.functor.prod s.functor) ⋙ a.closed.tensor
  finiteBalance : ∀ n : ℕ,
    ambient.tensor ⋙ (s.levels n).T ≅
      ((s.levels n).T.prod (s.levels n).T) ⋙ (a.levelClosed n).tensor
  finiteModel : ∀ n : ℕ, SemilinearSections.ScalarTensorComparisonModel.{c, v, r} J R (B n) (q n)
    (s.levels n) ambient (a.levelClosed n) ambientModels (a.levelTensorModels n)
      (finiteBalance n)
  ordinary : ∀ M N : SemilinearSections.Mod.{c, v, max c v r} J R,
    s.ordinary.obj (SemilinearSections.ordinaryTensor.{c, v, r} J R M N) ≅
      SemilinearSections.ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
        (s.ordinary.obj M) (s.ordinary.obj N)
  ordinary_evaluation : ∀ (n : ℕ) (M N : SemilinearSections.Mod.{c, v, max c v r} J R),
    (s.ordinaryEvaluation n).hom.app (SemilinearSections.ordinaryTensor.{c, v, r} J R M N) ≫
        ((finiteModel n).ordinary M N).hom =
      (SemilinearSections.evaluation.{c, v, max c v r} J B τ n).map (ordinary M N).hom ≫
        (SemilinearSections.ordinaryEvaluationTensor.{c, v, r} J B τ n (s.ordinary.obj M)
        (s.ordinary.obj N)).hom ≫
        SemilinearSections.ordinaryTensorHom.{c, v, r} J (B n) ((s.ordinaryEvaluation n).hom.app M)
          ((s.ordinaryEvaluation n).hom.app N)
  chain : ∀ P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    (SemilinearSections.totalTensor.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)).obj
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P,
          (s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      (s.ordinary.mapHomologicalComplex (.up ℤ)).obj ((SemilinearSections.totalTensor.{c, v, r} J
      R).obj (P, Q))
  summand : ∀ (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) (i j k : ℤ)
      (h : i + j = k),
    SemilinearSections.tensorSummand.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q) i j k h ≫ (chain P Q).f k =
      (ordinary (P.X i) (Q.X j)).inv ≫ s.ordinary.map (SemilinearSections.tensorSummand.{c, v, r}
      J R P Q i j k h)
  kflat : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P → SemilinearSections.flatTerms.{c, v,
      r} J R P →
    CochainComplex.IsKFlatIndependentCoefficients (R := SemilinearSections.systemRing.{c, v, max c
      v r} J B τ)
      ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  representative : ∀ (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (fP : SemilinearSections.flatTerms.{c, v, r} J R P) (fQ : SemilinearSections.flatTerms.{c, v,
      r} J R Q)
    (_hPQ : CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((SemilinearSections.totalTensor.{c, v, r} J R).obj (P, Q))),
    (SemilinearSections.tensorModelIso.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
      a.closed a.tensorModels ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q)
        (kflat P hP fP) (kflat Q hQ fQ)).hom ≫
      a.closed.tensor.map (Prod.mkHom
        (@asIso _ _ _ _ (s.epsilon.app P) (s.computes P hP)).inv
        (@asIso _ _ _ _ (s.epsilon.app Q) (s.computes Q hQ)).inv) ≫
      balance.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      s.functor.map (SemilinearSections.tensorModelIso.{c, v, r} J R ambient ambientModels P Q hP
      hQ).inv ≫
      s.epsilon.app ((SemilinearSections.totalTensor.{c, v, r} J R).obj (P, Q)) =
      DerivedCategory.Q.map (chain P Q)

/-- The canonical quotient-diagram context. All geometric adjunctions are the existing
module-induced adjunctions; all scalar operations are universal presentations with their
section formulas. Existence of this record is part of the theorem below, not a hypothesis.
Source: Stacks 0B56, 07A4, 07A6; Zheng 4.1
(blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
structure Presentation (J : GrothendieckTopology C) (K : GrothendieckTopology X)
    (A : Type (max c v r)) [CommRing A] (I : Ideal A)
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf K (Type (max c v r)))
    (uPush : Sheaf K (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) where
  geometry : RingedCoefficientProjection.Geometry uInv uPush adj
  source : SemilinearSections.Data.{c, v, r} J (finite.{c, v, r} J A I) (quotientTransition.{c, v,
      r} J A I)
  quotient : SemilinearSections.Geometry.{c, v, r} J (finite.{c, v, r} J A I)
    (quotientTransition.{c, v, r} J A I) source K uInv uPush adj
  qX : ∀ n : ℕ, geometry.rings.obj (constant.{c, v, r} J A) ⟶
    quotient.coefficients n
  qX_underlying : ∀ n : ℕ,
    uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map
        (quotientMap.{c, v, r} J A I n)) ≫
        (quotient.inverseImage n).ringUnderlying.hom =
      (geometry.inverse (constant.{c, v, r} J A)).ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{max c v r})).map (qX n)
  qX_transition : ∀ n : ℕ, qX (n + 1) ≫ quotient.coefficientTransition n = qX n
  y : Reduction.{c, v, r} J (constant.{c, v, r} J A) (finite.{c, v, r} J A I)
    (quotientTransition.{c, v, r} J A I) (quotientMap.{c, v, r} J A I)
  x : Reduction.{c, v, r} K (geometry.rings.obj (constant.{c, v, r} J A))
    quotient.coefficients quotient.coefficientTransition qX
  tensorY : TensorReduction.{c, v, r} y source
  tensorX : TensorReduction.{c, v, r} x quotient.target
  ordinaryPull : y.ordinary ⋙ quotient.pull ≅
    (geometry.inverse (constant.{c, v, r} J A)).modules ⋙ x.ordinary
  ordinaryPull_insertion : ∀ (n : ℕ) (M : SemilinearSections.Mod.{c, v, max c v r} J (constant.{c,
      v, r} J A)),
    uInv.map (y.insertion n M) ≫
        (quotient.inverseImage n).moduleUnderlying.inv.app
          ((SemilinearSections.evaluation.{c, v, max c v r} J (finite.{c, v, r} J A I)
            (quotientTransition.{c, v, r} J A I) n).obj (y.ordinary.obj M)) ≫
        (SemilinearSections.underlying.{c, v, r} K (quotient.coefficients n)).map
          ((quotient.ordinaryPullEvaluation n).inv.app (y.ordinary.obj M) ≫
            (SemilinearSections.evaluation.{c, v, max c v r} K quotient.coefficients
            quotient.coefficientTransition n).map
              (ordinaryPull.hom.app M)) =
      (geometry.inverse (constant.{c, v, r} J A)).moduleUnderlying.inv.app M ≫
        x.insertion n ((geometry.inverse (constant.{c, v, r} J A)).modules.obj M)
  pull : y.functor ⋙ quotient.pull.mapDerivedCategory ≅
    geometry.left (constant.{c, v, r} J A) ⋙ x.functor
  ordinaryPullComplex : y.ordinary.mapHomologicalComplex (.up ℤ) ⋙
      quotient.pull.mapHomologicalComplex (.up ℤ) ≅
    (geometry.inverse (constant.{c, v, r} J A)).modules.mapHomologicalComplex (.up ℤ) ⋙
      x.ordinary.mapHomologicalComplex (.up ℤ)
  ordinaryPullComplex_component : ∀
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J (constant.{c, v, r} J A)) ℤ)
      (i : ℤ),
    (ordinaryPullComplex.hom.app P).f i = ordinaryPull.hom.app (P.X i)
  pull_representative : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J
      (constant.{c, v, r} J A)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := constant.{c, v, r} J A) P →
    SemilinearSections.flatTerms.{c, v, r} J (constant.{c, v, r} J A) P →
    pull.hom.app (DerivedCategory.Q.obj P) ≫
        x.functor.map ((geometry.inverse (constant.{c, v, r} J
        A)).modules.mapDerivedCategoryFactors.hom.app P) ≫
        x.epsilon.app (((geometry.inverse (constant.{c, v, r} J A)).modules.mapHomologicalComplex
        (.up ℤ)).obj P) =
      quotient.pull.mapDerivedCategory.map (y.epsilon.app P) ≫
        quotient.pull.mapDerivedCategoryFactors.hom.app
          ((y.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (ordinaryPullComplex.hom.app P)

variable {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {A : Type (max c v r)} [CommRing A] {I : Ideal A}
  {uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf K (Type (max c v r))}
  {uPush : Sheaf K (Type (max c v r)) ⥤ Sheaf J (Type (max c v r))}
  {adj : uInv ⊣ uPush} (p : Presentation.{c, v, r} J K A I uInv uPush adj)

/-- The coefficient mate, transposed from the reduction of the ambient counit.
Source: Stacks 07A6, 0B56 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
def coefficientMate (H : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj
      (constant.{c, v, r} J A))) :
    p.y.functor.obj ((p.geometry.right (constant.{c, v, r} J A)).obj H) ⟶
      p.quotient.push.rightDerivedFunctor.obj (p.x.functor.obj H) :=
  p.quotient.adjunction.homEquiv _ _
    (p.pull.hom.app ((p.geometry.right (constant.{c, v, r} J A)).obj H) ≫
      p.x.functor.map ((p.geometry.adjunction (constant.{c, v, r} J A)).counit.app H))

/-- The target balancing uses the same pullback/scalar isomorphism as the coefficient mate.
Source: Stacks 07A4 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
def targetBalance (H : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj
      (constant.{c, v, r} J A)))
    (L : SemilinearSections.D.{c, v, max c v r} J (constant.{c, v, r} J A)) :
    p.x.functor.obj (p.tensorX.ambient.tensor.obj
        (H, (p.geometry.left (constant.{c, v, r} J A)).obj L)) ≅
      p.quotient.target.closed.tensor.obj
        (p.x.functor.obj H, p.quotient.pull.mapDerivedCategory.obj (p.y.functor.obj L)) :=
  p.tensorX.balance.app (H, (p.geometry.left (constant.{c, v, r} J A)).obj L) ≪≫
    p.quotient.target.closed.tensor.mapIso
      ((Iso.refl (p.x.functor.obj H)).prod (p.pull.app L).symm)

/-- The single morphism before evaluation, with source M and target P_B R_X N.
Source: Stacks 0B56 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
def arrow (H : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r}
      J A)))
    (L : SemilinearSections.D.{c, v, max c v r} J (constant.{c, v, r} J A)) :
    p.y.functor.obj (p.tensorY.ambient.tensor.obj
        ((p.geometry.right (constant.{c, v, r} J A)).obj H, L)) ⟶
      p.quotient.push.rightDerivedFunctor.obj (p.x.functor.obj
        (p.tensorX.ambient.tensor.obj
          (H, (p.geometry.left (constant.{c, v, r} J A)).obj L))) :=
  p.tensorY.balance.hom.app ((p.geometry.right (constant.{c, v, r} J A)).obj H, L) ≫
    p.source.closed.tensor.map (Prod.mkHom (coefficientMate p H) (𝟙 _)) ≫
    p.quotient.tensorProjection J (finite.{c, v, r} J A I)
      (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj
        (p.x.functor.obj H) (p.y.functor.obj L) ≫
    p.quotient.push.rightDerivedFunctor.map (targetBalance p H L).inv

/-- The evaluated coefficient mate, using the actual direct-image comparison.
Source: Stacks 07A6 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
def finiteMate (n : ℕ) (H : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj
      (constant.{c, v, r} J A))) :
    (p.y.levels n).T.obj ((p.geometry.right (constant.{c, v, r} J A)).obj H) ⟶
      (p.quotient.levelPush n).rightDerivedFunctor.obj ((p.x.levels n).T.obj H) :=
  (p.y.evaluation n).inv.app ((p.geometry.right (constant.{c, v, r} J A)).obj H) ≫
    (SemilinearSections.e.{c, v, max c v r} J (finite.{c, v, r} J A I) (quotientTransition.{c, v,
      r} J A I) n).map
      (coefficientMate p H) ≫
    (p.quotient.pushEvaluation n).hom.app (p.x.functor.obj H) ≫
    (p.quotient.levelPush n).rightDerivedFunctor.map ((p.x.evaluation n).hom.app H)

/-- The finite pullback/scalar comparison induced by the specified system square.
Source: Stacks 07A4, 07A6
(blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
def finitePull (n : ℕ) (L : SemilinearSections.D.{c, v, max c v r} J (constant.{c, v, r} J A)) :
    (SemilinearSections.derivedExact.{c, v, max c v r, c, v} J K (finite.{c, v, r} J A I n)
      (p.quotient.coefficients n)
        (p.quotient.inverseImage n).modules).obj ((p.y.levels n).T.obj L) ≅
      (p.x.levels n).T.obj ((p.geometry.left (constant.{c, v, r} J A)).obj L) :=
  (SemilinearSections.derivedExact.{c, v, max c v r, c, v} J K (finite.{c, v, r} J A I n)
      (p.quotient.coefficients n)
      (p.quotient.inverseImage n).modules).mapIso ((p.y.evaluation n).app L).symm ≪≫
    ((p.quotient.pullEvaluation n).app (p.y.functor.obj L)).symm ≪≫
    (SemilinearSections.e.{c, v, max c v r} K p.quotient.coefficients
      p.quotient.coefficientTransition n).mapIso (p.pull.app L) ≪≫
    (p.x.evaluation n).app ((p.geometry.left (constant.{c, v, r} J A)).obj L)

/-- The balanced finite target has coefficient ring A/(I^(n+1)), on both tensor factors.
Source: Stacks 07A4 (blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
def finiteTargetBalance (n : ℕ)
    (H : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r} J A)))
    (L : SemilinearSections.D.{c, v, max c v r} J (constant.{c, v, r} J A)) :
    (p.x.levels n).T.obj (p.tensorX.ambient.tensor.obj
        (H, (p.geometry.left (constant.{c, v, r} J A)).obj L)) ≅
      (p.quotient.target.levelClosed n).tensor.obj
        ((p.x.levels n).T.obj H,
          (SemilinearSections.derivedExact.{c, v, max c v r, c, v} J K (finite.{c, v, r} J A I n)
          (p.quotient.coefficients n)
            (p.quotient.inverseImage n).modules).obj ((p.y.levels n).T.obj L)) :=
  (p.tensorX.finiteBalance n).app
      (H, (p.geometry.left (constant.{c, v, r} J A)).obj L) ≪≫
    (p.quotient.target.levelClosed n).tensor.mapIso
      ((Iso.refl ((p.x.levels n).T.obj H)).prod (finitePull p n L).symm)

/-- Evaluation, its counit normalization, naturality, and every quotient transition.
All equations concern the single morphism `arrow`, not unrelated level morphisms.
Source: Stacks 0B56, 07A4, 07A6; Zheng 4.1
(blueprint: lem-pur-quotient-diagram-projection-evaluation). -/
structure Laws : Prop where
  transition : p.quotient.TransitionFormula J (finite.{c, v, r} J A I)
    (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj
  pullTransition : p.quotient.PullTransitionFormula J (finite.{c, v, r} J A I)
    (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj
  coefficient_counit : ∀ (n : ℕ)
    (H : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r} J A))),
    (SemilinearSections.derivedExact.{c, v, max c v r, c, v} J K (finite.{c, v, r} J A I n)
      (p.quotient.coefficients n)
        (p.quotient.inverseImage n).modules).map (finiteMate p n H) ≫
        (p.quotient.derivedLevelAdjunction n).counit.app ((p.x.levels n).T.obj H) =
      (finitePull p n ((p.geometry.right (constant.{c, v, r} J A)).obj H)).hom ≫
        (p.x.levels n).T.map
          ((p.geometry.adjunction (constant.{c, v, r} J A)).counit.app H)
  evaluation : ∀ (n : ℕ)
    (H : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r} J A)))
    (L : SemilinearSections.D.{c, v, max c v r} J (constant.{c, v, r} J A)),
    (SemilinearSections.e.{c, v, max c v r} J (finite.{c, v, r} J A I) (quotientTransition.{c, v,
      r} J A I) n).map
        (arrow p H L) ≫
        (p.quotient.pushEvaluation n).hom.app (p.x.functor.obj
          (p.tensorX.ambient.tensor.obj
            (H, (p.geometry.left (constant.{c, v, r} J A)).obj L))) ≫
        (p.quotient.levelPush n).rightDerivedFunctor.map
          ((p.x.evaluation n).hom.app (p.tensorX.ambient.tensor.obj
              (H, (p.geometry.left (constant.{c, v, r} J A)).obj L)) ≫
            (finiteTargetBalance p n H L).hom) =
      (p.y.evaluation n).hom.app (p.tensorY.ambient.tensor.obj
          ((p.geometry.right (constant.{c, v, r} J A)).obj H, L)) ≫
        (p.tensorY.finiteBalance n).hom.app
          ((p.geometry.right (constant.{c, v, r} J A)).obj H, L) ≫
        (p.source.levelClosed n).tensor.map (Prod.mkHom (finiteMate p n H) (𝟙 _)) ≫
        p.quotient.levelTensorProjection J (finite.{c, v, r} J A I)
          (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj n
            ((p.x.levels n).T.obj H) ((p.y.levels n).T.obj L)
  naturality : ∀
    (H H' : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r} J
      A)))
    (L L' : SemilinearSections.D.{c, v, max c v r} J (constant.{c, v, r} J A)) (h : H ⟶ H') (k : L
      ⟶ L'),
    p.y.functor.map (p.tensorY.ambient.tensor.map
        (Prod.mkHom ((p.geometry.right (constant.{c, v, r} J A)).map h) k)) ≫
        arrow p H' L' =
      arrow p H L ≫ p.quotient.push.rightDerivedFunctor.map
        (p.x.functor.map (p.tensorX.ambient.tensor.map
          (Prod.mkHom h ((p.geometry.left (constant.{c, v, r} J A)).map k))))

/-- Finite-coefficient evaluation of the canonical quotient-diagram projection mate.
Source: Stacks 0B56 (equation-projection-formula-map), 07A4
(lemma-pullback-tensor-product), 07A6 (lemma-adjoint); Zheng Construction 4.1, p. 21.
(blueprint: lem-pur-quotient-diagram-projection-evaluation).

Proof:
1. Use system-ringed-sequence-site, system-level-left-extension and
system-evaluation-topos to realize the quotient ring, exact evaluation and its singleton
left adjoints on the ordinary strict-system derived category. Projection-mate-exact
supplies the diagram adjunction and its canonical tensor projection.
2. On a flat-term K-flat complex, the singleton extension at m <= n is B_m tensor Q
and is zero otherwise. Tensor pullback commutes with it on every local tensor, including
the quotient transitions, by system-single-derived-extension, ordinary-single-extension
and ringed-pullback-preserves-kflat. Vertical covers give K-flatness on the sequence site.
3. Compose the singleton and geometric Hom adjunctions. Uniqueness of right adjoints
identifies evaluated direct image with the finite direct image. Track the identity
through the composite transpose: its counit is exactly the evaluated diagram counit.
4. Paste scalar-restriction/direct-image comparisons using
 diagram-ring-restriction-pushforward, ringed-topoi-derived-pushforward-composition and
 tower-derived-evaluation-normalization. The two pastings have the same ordinary scalar
transpose x tensor b mapped to b g(x), so have the same counit normalization.
5. For a flat-term K-flat representative Q, Delta Q is K-flat and reduction is the
actual system (Q tensor B_m)_m. Its unit is x mapped to x tensor 1. Canonical scalar
tensor balancing is multiplication of the two coefficient factors. This gives precisely
the ordinary, total-summand and universal representative equations in Presentation.
6. Evaluate the transpose defining coefficientMate and use step 3. The result is the
coefficient_counit identity, hence the specified finite coefficient mate.
7. Apply ringed-exchange-tensor-coherence to the evaluation square. Its exchange is the
step-3 comparison because their transposes are the same counit. Thus evaluation carries
the diagram projection to the counit-defined finite projection.
8. Evaluate the single composite arrow. Substitute steps 5--7 and cancel inverse tensor
and pullback comparisons. This gives Laws.evaluation. Naturality of its factors gives
Laws.naturality simultaneously in H and L.
9. For m >= n, system-single-derived-evaluation identifies the singleton transpose with
the actual m-to-n transition. The Hom chain of step 3 intertwines these transposes.
The scalar tensor calculation sends both routes to (x tensor y) tensor a-bar b-bar.
It therefore preserves every transition, including m=n. This proves both transition
formulas. No assertion about preservation of K-injectives by evaluation, and no flatness,
perfectness or completeness hypothesis, occurs. -/
theorem quotientDiagramProjectionEvaluation
    (J : GrothendieckTopology C) (K : GrothendieckTopology X)
    (A : Type (max c v r)) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf K (Type (max c v r)))
    (uPush : Sheaf K (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv] :
    ∃ p : Presentation.{c, v, r} J K A I uInv uPush adj, Laws.{c, v, r} p := by
  sorry

end SheafOfModules.QuotientDiagramProjection
