/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Types.Basic
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Paper.PbcCompletedPullbackActual
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Direct image and evaluation of strict coefficient systems

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21,
and Lemma 4.10, printed pp. 23--24
(blueprint: lem-pur-coefficient-system-derived-comparison).

The index `n` denotes the positive exponent `n+1`. All systems, evaluation functors,
scalar extensions and adjoint transitions are the recorded coefficient-evaluation
interface. The structures below specify the geometric lifts and the comparison,
including their normalizations; they are conclusions, not hypotheses of the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w d a b av bv
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

/-- The existing forgetful functor at a coefficient level.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-coefficient-system-derived-comparison). -/
abbrev coefficientUnderlying (n : ℕ) :
    coefficientLevelModules (J := J) O ell n ⥤ Sheaf J (Type w) :=
  toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

/-- Constant coefficient generators, obtained from the actual ring-sheafification unit.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-coefficient-system-derived-comparison). -/
def coefficientConstantSection (n : ℕ)
    (x : O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) :
    (constantSheaf J (Type w)).obj PUnit ⟶
      (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj
        (coefficientQuotientSheaf (J := J) O ell n) :=
  ((sheafificationAdjunction J (Type w)).homEquiv _ _).symm
    ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{w+1}) ↦ x)) ≫
      whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))))
          (CategoryTheory.forget CommRingCat.{w}))

/-- Scalar restriction leaves the underlying sheaf of sets unchanged.
Source: Stacks 03CZ (blueprint: lem-pur-coefficient-system-derived-comparison). -/
def coefficientRestrictionUnderlying {m n : ℕ} (h : n ≤ m) :
    coefficientRestriction (J := J) O ell h ⋙ coefficientUnderlying (J := J) O ell m ≅
      coefficientUnderlying (J := J) O ell n :=
  isoWhiskerRight (siteScalarUnderlyingIso
    (coefficientQuotientMap (J := J) O ell h))
      (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w}))

section DerivedAdjunction
variable {A : Type a} {B : Type b} [Category.{av} A] [Category.{bv} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)

/-- Exact inverse image and total right direct image, with their normalized adjunction.
The universal right-derived pair and its K-injective comparison fix the right functor;
the transpose equation fixes its adjunction relative to the ordinary one.
Source: Zheng, Lemma 4.10; Stacks 09T5, 0FND
(blueprint: lem-pur-coefficient-system-derived-comparison). -/
structure CoefficientDerivedImage where
  inverse : DerivedCategory A ⥤ DerivedCategory B
  inverseFactors : DerivedCategory.Q ⋙ inverse ≅
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  direct : DerivedCategory B ⥤ DerivedCategory A
  directUnit : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ direct
  isRightDerived : direct.IsRightDerivedFunctor directUnit
    (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex B ℤ, I.IsKInjective → IsIso (directUnit.app I)
  adjunction : inverse ⊣ direct
  transpose : ∀ (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
      (inverseFactors.hom.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv P I f) ≫ directUnit.app I
end DerivedAdjunction

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

/-- The ordinary level and system images. The algebraic lift transports all operations;
constants are fixed on every coefficient generator, and the displayed Hom formula is
the underlying set-sheaf adjunction. Evaluation and transition equations fix the actual
levelwise system functors, on objects and maps, rather than arbitrary adjoint functors.
Source: Zheng, Construction 4.1, and the paragraph before Lemma 4.10
(blueprint: lem-pur-coefficient-system-derived-comparison). -/
structure CoefficientSystemOrdinaryImage where
  singleton : L.obj ((constantSheaf J (Type w)).obj PUnit) ≅
    (constantSheaf K (Type w)).obj PUnit
  lift : ∀ n, AlgebraicInverseImage L
    (coefficientQuotientSheaf (J := J) O ell n)
    (coefficientQuotientSheaf (J := K) O ell n)
  constants : ∀ n x,
    L.map (coefficientConstantSection (J := J) O ell n x) ≫ (lift n).ringUnderlying.hom =
      singleton.hom ≫ coefficientConstantSection (J := K) O ell n x
  [inverseAdditive : ∀ n, (lift n).modules.Additive]
  inverseExact : ∀ n, PreservesFiniteLimits (lift n).modules ∧
    PreservesFiniteColimits (lift n).modules
  right : ∀ n, coefficientLevelModules (J := K) O ell n ⥤
    coefficientLevelModules (J := J) O ell n
  [rightAdditive : ∀ n, (right n).Additive]
  rightUnderlying : ∀ n, right n ⋙ coefficientUnderlying (J := J) O ell n ≅
    coefficientUnderlying (J := K) O ell n ⋙ V
  levelAdj : ∀ n, (lift n).modules ⊣ right n
  levelTranspose : ∀ n M N (f : (lift n).modules.obj M ⟶ N),
    (coefficientUnderlying (J := J) O ell n).map ((levelAdj n).homEquiv M N f) ≫
      (rightUnderlying n).hom.app N =
    adj.homEquiv _ _ ((lift n).moduleUnderlying.inv.app M ≫
      (coefficientUnderlying (J := K) O ell n).map f)
  restrictInverse : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := J) O ell h ⋙ (lift m).modules ≅
      (lift n).modules ⋙ coefficientRestriction (J := K) O ell h
  restrictInverseUnderlying : ∀ {m n : ℕ} (h : n ≤ m) M,
    (coefficientUnderlying (J := K) O ell m).map ((restrictInverse h).hom.app M) ≫
      (coefficientRestrictionUnderlying (J := K) O ell h).hom.app
        ((lift n).modules.obj M) ≫ (lift n).moduleUnderlying.hom.app M =
    (lift m).moduleUnderlying.hom.app ((coefficientRestriction (J := J) O ell h).obj M) ≫
      L.map ((coefficientRestrictionUnderlying (J := J) O ell h).hom.app M)
  inverse : CoefficientSystem (J := J) O ell ⥤ CoefficientSystem (J := K) O ell
  rightSystem : CoefficientSystem (J := K) O ell ⥤ CoefficientSystem (J := J) O ell
  [systemInverseAdditive : inverse.Additive]
  [systemRightAdditive : rightSystem.Additive]
  systemExact : PreservesFiniteLimits inverse ∧ PreservesFiniteColimits inverse
  inverseEvaluation : ∀ n, inverse ⋙ coefficientEvaluation (J := K) n ≅
    coefficientEvaluation (J := J) n ⋙ (lift n).modules
  rightEvaluation : ∀ n, rightSystem ⋙ coefficientEvaluation (J := J) n ≅
    coefficientEvaluation (J := K) n ⋙ right n
  inverseTransition : ∀ n M,
    ((inverse.obj M).transition n) ≫
      (coefficientRestriction (J := K) O ell (Nat.le_succ n)).map
        ((inverseEvaluation n).hom.app M) =
    (inverseEvaluation (n + 1)).hom.app M ≫ (lift (n + 1)).modules.map (M.transition n) ≫
      (restrictInverse (Nat.le_succ n)).hom.app (M.level n)
  systemAdj : inverse ⊣ rightSystem
  systemTranspose : ∀ M N (f : inverse.obj M ⟶ N) n,
    (coefficientEvaluation (J := J) n).map ((systemAdj.homEquiv M N) f) ≫
      (rightEvaluation n).hom.app N =
    (levelAdj n).homEquiv (M.level n) (N.level n)
      ((inverseEvaluation n).inv.app M ≫ (coefficientEvaluation (J := K) n).map f)

attribute [instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := K) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := K) O ell)]

/-- Normalization means invertibility of the actual adjoint derived transitions.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-coefficient-system-derived-comparison). -/
def IsNormalizedCoefficientSystem
    (P : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (M : DerivedCategory (CoefficientSystem (J := J) O ell)) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m), IsIso
    (((P.scalar h).derivedAdj.homEquiv ((P.evaluation m).obj M)
      ((P.evaluation n).obj M)).symm ((P.transition h).app M))

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 800000 in
-- Elaborate the canonical comparison equations against both evaluation packages.
/-- The full derived comparison and its coherence on systems and all derived maps.
Every functor is tied to the ordinary geometric functors or to the universal derived
scalar extension; the two adjunction equations fix the evaluation comparison.
Source: Zheng, Construction 4.1 and Lemma 4.10
(blueprint: lem-pur-coefficient-system-derived-comparison). -/
structure CoefficientSystemDerivedImage
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)) where
  system : CoefficientDerivedImage S.inverse S.rightSystem S.systemAdj
  level : ∀ n, CoefficientDerivedImage (S.lift n).modules (S.right n) (S.levelAdj n)
  inverseEvaluation : ∀ n, system.inverse ⋙ PX.evaluation n ≅
    PY.evaluation n ⋙ (level n).inverse
  inverseEvaluation_rep : ∀ n H,
    (inverseEvaluation n).hom.app (DerivedCategory.Q.obj H) ≫
      (level n).inverse.map ((PY.evaluationFactors n).hom.app H) ≫
      (level n).inverseFactors.hom.app
        (((coefficientEvaluation (J := J) n).mapHomologicalComplex (.up ℤ)).obj H) =
    (PX.evaluation n).map (system.inverseFactors.hom.app H) ≫
      (PX.evaluationFactors n).hom.app ((S.inverse.mapHomologicalComplex (.up ℤ)).obj H) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (S.inverseEvaluation n) (.up ℤ)).hom.app H)
  directEvaluation : ∀ n, system.direct ⋙ PY.evaluation n ≅
    PX.evaluation n ⋙ (level n).direct
  counit : ∀ n M,
    (inverseEvaluation n).hom.app (system.direct.obj M) ≫
      (level n).inverse.map ((directEvaluation n).hom.app M) ≫
      (level n).adjunction.counit.app ((PX.evaluation n).obj M) =
    (PX.evaluation n).map (system.adjunction.counit.app M)
  unit : ∀ n H,
    (PY.evaluation n).map (system.adjunction.unit.app H) ≫
      (directEvaluation n).hom.app (system.inverse.obj H) ≫
      (level n).direct.map ((inverseEvaluation n).hom.app H) =
    (level n).adjunction.unit.app ((PY.evaluation n).obj H)
  tensor : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientTensor (J := J) (O := O) (ell := ell) h ⋙ (S.lift n).modules ≅
      (S.lift m).modules ⋙ coefficientTensor (J := K) (O := O) (ell := ell) h
  tensor_unit : ∀ {m n : ℕ} (h : n ≤ m) M,
    (S.lift m).modules.map ((coefficientTensorAdj (J := J) h).unit.app M) ≫
      (S.restrictInverse h).hom.app ((coefficientTensor (J := J) h).obj M) ≫
      (coefficientRestriction (J := K) O ell h).map ((tensor h).hom.app M) =
    (coefficientTensorAdj (J := K) h).unit.app ((S.lift m).modules.obj M)
  derivedTensor : ∀ {m n : ℕ} (h : n ≤ m),
    (PY.scalar h).derived ⋙ (level n).inverse ≅
      (level m).inverse ⋙ (PX.scalar h).derived
  derivedTensor_rep : ∀ {m n : ℕ} (h : n ≤ m) P,
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell m) P →
    (∀ i : ℤ, IsFlatOnSite (R := coefficientQuotientSheaf (J := J) O ell m) (P.X i)) →
    (derivedTensor h).hom.app (DerivedCategory.Q.obj P) ≫
      (PX.scalar h).derived.map ((level m).inverseFactors.hom.app P) ≫
      (PX.scalar h).counit.app (((S.lift m).modules.mapHomologicalComplex (.up ℤ)).obj P) =
    (level n).inverse.map ((PY.scalar h).counit.app P) ≫
      (level n).inverseFactors.hom.app
        (((coefficientTensor (J := J) h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (tensor h) (.up ℤ)).hom.app P)
  restrictedDirect : ∀ {m n : ℕ} (h : n ≤ m),
    (PX.scalar h).restriction ⋙ (level m).direct ≅
      (level n).direct ⋙ (PY.scalar h).restriction
  restrictedDirect_mate : ∀ {m n : ℕ} (h : n ≤ m) A B
    (f : (level n).inverse.obj ((PY.scalar h).derived.obj A) ⟶ B),
    (PY.scalar h).derivedAdj.homEquiv A ((level n).direct.obj B)
      ((level n).adjunction.homEquiv _ B f) =
    (level m).adjunction.homEquiv A ((PX.scalar h).restriction.obj B)
      ((PX.scalar h).derivedAdj.homEquiv ((level m).inverse.obj A) B
        ((derivedTensor h).inv.app A ≫ f)) ≫ (restrictedDirect h).hom.app B
  restrictedInverse : ∀ {m n : ℕ} (h : n ≤ m),
    (PY.scalar h).restriction ⋙ (level m).inverse ≅
      (level n).inverse ⋙ (PX.scalar h).restriction
  restrictedInverse_mate : ∀ {m n : ℕ} (h : n ≤ m) A,
    (level m).adjunction.homEquiv _ _ ((restrictedInverse h).hom.app A) =
      (PY.scalar h).restriction.map ((level n).adjunction.unit.app A) ≫
        (restrictedDirect h).inv.app ((level n).inverse.obj A)
  inverseTransition : ∀ {m n : ℕ} (h : n ≤ m) H,
    (PX.transition h).app (system.inverse.obj H) ≫
      (PX.scalar h).restriction.map ((inverseEvaluation n).hom.app H) =
    (inverseEvaluation m).hom.app H ≫ (level m).inverse.map ((PY.transition h).app H) ≫
      (restrictedInverse h).hom.app ((PY.evaluation n).obj H)
  directTransition : ∀ {m n : ℕ} (h : n ≤ m) M,
    (PY.transition h).app (system.direct.obj M) ≫
      (PY.scalar h).restriction.map ((directEvaluation n).hom.app M) =
    (directEvaluation m).hom.app M ≫ (level m).direct.map ((PX.transition h).app M) ≫
      (restrictedDirect h).hom.app ((PX.evaluation n).obj M)
  detectsIso : ∀ {M N : DerivedCategory (CoefficientSystem (J := K) O ell)} (f : M ⟶ N),
    IsIso f ↔ ∀ n : ℕ, IsIso ((PX.evaluation n).map f)
  boundedBelow : ∀ M : DerivedCategory (CoefficientSystem (J := K) O ell),
    (∃ a : ℤ, M.IsGE a) → ∃ a : ℤ, (system.direct.obj M).IsGE a
  origin :
    (∀ n (A B : DerivedCategory (coefficientLevelModules (J := J) O ell n)),
      (∃ a : ℤ, A.IsGE a) → (∃ b : ℤ, B.IsGE b) →
      Function.Bijective ((level n).inverse.map : (A ⟶ B) → _)) →
    ∀ M : DerivedCategory (CoefficientSystem (J := K) O ell),
      (∃ a : ℤ, M.IsGE a) →
      (∀ n, ∃ H : DerivedCategory (coefficientLevelModules (J := J) O ell n),
        (∃ a : ℤ, H.IsGE a) ∧
        Nonempty ((level n).inverse.obj H ≅ (PX.evaluation n).obj M)) →
      IsIso (system.adjunction.counit.app M) ∧
        (IsNormalizedCoefficientSystem O ell PX M →
          IsNormalizedCoefficientSystem O ell PY (system.direct.obj M))

set_option maxHeartbeats 800000 in
-- Instantiate both sites and all ordinary/derived coherence structures.
/-- Derived direct image commutes canonically with every evaluation, with the specified
unit, counit and coefficient-change compatibility; bounded-below objects of levelwise
origin descend, and normalized ones stay normalized.
Source: Zheng, Construction 4.1 and Lemma 4.10, printed pp. 21, 23--24
(blueprint: lem-pur-coefficient-system-derived-comparison).

Proof plan:
1. Present strict systems as modules on the product sequence site. Kernels and cokernels
are levelwise. Apply prop-pur-kinjective-resolutions-exist on this small ringed site.
Transport algebraic operations through the geometric inverse image, which is exact;
its adjunction on modules gives the system adjunction level by level. Apply
lem-weil-pbc-exact-functor-derived-factorization and
lem-weil-pbc-kinjective-total-derived to construct the derived functors.
2. Use lem-weil-pbc-termwise-adjunction-homotopy and
lem-pc-pre-derived-adjoint-functors-general to normalize the derived adjunctions.
Their transpose on a strict complex map is the ordinary transpose followed by the
universal right-derived comparison, exactly the equation in CoefficientDerivedImage.
3. Resolve a coefficient-level complex by a flat-term K-flat complex, using
lem-pc-kflat-resolution. Its extension E_n has zero components above n and quotient
tensors below n. Exact inverse image preserves the cokernel of multiplication by
ell^(q+1), so commutes with these quotient tensors and their reduction maps.
Use lem-weil-pbc-ringed-topoi-derived-tensor-pullback for the canonical comparison.
4. The same flat-term K-flat computation gives the derived coefficient-change
comparison for every quotient, by lem-pur-derived-change-of-rings and
lem-weil-pbc-ringed-pullback-preserves-kflat. No quotient map is assumed flat.
5. Apply the LE_n/e_n adjunction of
lem-pur-coefficient-evaluation-derived-left-adjoint on both sides, the derived
system adjunction, and the comparison of step 3. The resulting natural chain of
Hom bijections identifies e_n Ru_* with Ru_* e_n by Yoneda. Inverse image commutes
with evaluation already on strict complexes.
6. The n-component of the extension comparison is the identity. The normalized
transposes therefore give the evaluated counit equation. Compose it with the
system unit and use the triangle identity; uniqueness of transpose gives the unit
equation. Thus these comparisons are adjunction mates, not unspecified isomorphisms.
7. Tensor extension is left adjoint to exact scalar restriction. Apply
lem-pc-derived-adjoint-functors and normalize as in step 2. Composition of ringed-topos
direct images gives the restricted-direct-image comparison
(lem-weil-pbc-ringed-topoi-derived-pushforward-composition). Its mate equation fixes it.
8. The extension comparison commutes with the sigma maps of the evaluation dependency:
on K-flat representatives their components below n are the same quotient tensor maps,
and above n have zero source. Its explicit sigma-mate formula gives the transition
squares. Naturality gives compatibility for every derived system morphism, including
identity quotients and compositions, with no independent choice of levelwise lifts.
9. For a uniformly bounded-below input choose a bounded-below injective resolution
(lem-sc-bounded-below-injective-resolution), which is K-injective and computes the
same total derived functor. Left exactness and
lem-weil-pbc-derived-functor-negative-vanishing give a uniform lower bound.
10. Full faithfulness on bounded-below level categories makes the level units
invertible by Yoneda. Triangle identities and naturality make the counit invertible
on the essential image. Step 6 identifies each evaluated system counit with it.
Evaluations jointly detect derived isomorphisms because cohomology is levelwise.
11. Apply naturality of the system counit to each adjoint transition. The tensor
comparison identifies this square with epsilon_n u^*(t_N) = t_M C(epsilon_m).
If M is normalized, all arrows but u^*(t_N) are invertible by step 10. Full
faithfulness on bounded-below derived objects implies full faithfulness on module
sheaves, using the fully faithful degree-zero single functors
(lem-weil-pbc-derived-single-fully-faithful). Hence exact inverse image reflects zero
module sheaves. It commutes with cohomology, so it reflects acyclicity of arbitrary
complexes, and therefore reflects isomorphisms even for the possibly unbounded
coefficient-change objects. Apply this to t_N to conclude normalization.
12. For the pro-etale/etale morphism use the recorded
Scheme.proEtaleSiteComparison and ProEtale.siteComparison_boundedBelow for finite
quotient coefficients. Its inverse image satisfies exactly the required full
faithfulness hypothesis. No constructibility of the individual sheaves is needed.
-/
theorem coefficientSystemDerivedComparison
    [PreservesFiniteLimits L]
    (hregular : ∀ x : O, ell * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span ({ell} : Set O)) O] :
    ∃ (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
      (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
      (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)),
      Nonempty (CoefficientSystemDerivedImage O ell L V adj S PY PX) := by
  sorry

end SheafOfModules
