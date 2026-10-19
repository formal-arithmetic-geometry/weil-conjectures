/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Sheaf.SixFunctors.ArbitraryFieldVerdier
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.SfConstructibleHeart
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion

import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.SfImmersionCompletedPullbackComparison
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.CompactificationCoherence
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Paper.PbcRationalCategory
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Sheaf.Paper.AdicExceptionalProjection
import Sheaf.Paper.PbcScalarExtension
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.QbarOrdinaryAdjunction

/-! # Verdier-compatible common-stage recollement

Source: Bhatt--Scholze 6.7.2, 6.7.7, 6.7.19--20, 6.8.14--15
(blueprint: lem-per-qbar-dual-recollement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures


variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime]
  [Fact (IsUnit (l : k))] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (W : PerAdic.Base k)

/-- The standard t-structure on the actual intrinsic common-stage category.
Source: Bhatt--Scholze 6.8.11--15 (blueprint: lem-per-qbar-dual-recollement).
Proof: truncate the completed integral complexes. The stratified-perfect criterion
preserves constructibility, including the compatible etale origins. Rationalize
these truncations; their classes are the isomorphism closures of the integral
classes. Finite free coefficient extension is t-exact. Descend truncation triangles
to common finite stages. Orthogonality is checked there and passes to Hom colimits.
Every object has finite bounds at its representing stage. The two indexed standard
classes determine the t-structure uniquely. This argument uses only separated
finite type over the given field, not a finite-field model. -/
theorem sfArbitraryBaseStandard_existsUnique :
    ∃! t : Triangulated.TStructure
        (generalAlgebraicallyClosedConstructibleCategory l Ω W.scheme),
      (∀ n : ℤ, t.le n = sfCommonStageStandardClass l W.scheme Ω true n ∧
        t.ge n = sfCommonStageStandardClass l W.scheme Ω false n) ∧
      ∀ K, t.bounded K := by
  sorry

/-- Standard t-structure fixed by the existing intrinsic finite-stage classes.
Source: Bhatt--Scholze 6.8.11--15 (blueprint: lem-per-qbar-dual-recollement). -/
def sfArbitraryBaseStandard : Triangulated.TStructure
    (generalAlgebraicallyClosedConstructibleCategory l Ω W.scheme) :=
  (sfArbitraryBaseStandard_existsUnique l Ω W).exists.choose


end WeilConjectures

namespace WeilConjectures.QbarDualRecollement
open ArbitraryFieldVerdier

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime]
  [hk : Fact (IsUnit (l : k))]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

variable (B : ∀ W : PerAdic.Base k, Datum l hk.out Ω (𝟙 W.scheme))
  (P : ∀ W : PerAdic.Base k, Properties l hk.out Ω (B W))

/-- The relative dual is the actual internal Hom into the structure-map dualizing object.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-dual-recollement). -/
def dual (W : PerAdic.Base k) := (B W).dualY l hk.out Ω

/-- Exceptional closed restriction is literally D_Z i* D_X.
Source: Bhatt--Scholze 6.7.19--20 (blueprint: lem-per-qbar-dual-recollement). -/
def exceptional {Z X : PerAdic.Base k} (i : Z.scheme ⟶ X.scheme) :=
  (dual l Ω B X).rightOp ⋙ (pull l hk.out Ω i).op ⋙ dual l Ω B Z

/-- Exactness on the existing common-stage triangulations.
Source: Bhatt--Scholze 6.8.14--15 (blueprint: lem-per-qbar-dual-recollement). -/
def Exact {V W : PerAdic.Base k}
    (F : generalAlgebraicallyClosedConstructibleCategory l Ω V.scheme ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω W.scheme) : Prop :=
  F.Additive ∧ ∃ s : F.CommShift ℤ,
    (fun [_s : F.CommShift ℤ] ↦ F.IsTriangulated) (_s := s)

/-- Cohomology means the dependency's truncation formula on the intrinsic standard classes.
Source: Bhatt--Scholze 6.8.11--15 (blueprint: lem-per-qbar-dual-recollement). -/
def cohomology (W : PerAdic.Base k) (n : ℤ) :=
  PerAdic.cohomology (sfArbitraryBaseStandard l Ω W) n

/-- The rational-stage dual supplied by the same structure-adjunction scalar theorem.
Source: Bhatt--Scholze 6.8.14--15 (blueprint: lem-per-qbar-dual-recollement). -/
def rationalDatum (W : PerAdic.Base k) (E : AlgebraicallyClosedCoefficients.Index l Ω) :=
  (P W).scalar_compatible.choose E

/-- Its finite-stage dual is the recorded rational internal Hom, with trace normalization.
Source: Bhatt--Scholze 6.8.14--15 (blueprint: lem-per-qbar-dual-recollement). -/
def rationalDual (W : PerAdic.Base k) (E : AlgebraicallyClosedCoefficients.Index l Ω) :=
  (rationalDatum l Ω B P W E).dualY l hk.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)

/-- The dual inclusion is fixed by the structure trace, evaluation and coefficient unit.
Source: Bhatt--Scholze 6.8.14--15 (blueprint: lem-per-qbar-dual-recollement). -/
def dualInclusion (W : PerAdic.Base k) (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W.scheme E) :=
  dualYInclusion l hk.out Ω (B W) E (rationalDatum l Ω B P W E) K

/-- Exact completed restriction commutes with standard cohomology and geometric fibres.
The fibre functors are constrained by their actual finite-stage section normalization.
Source: Bhatt--Scholze 6.7.2, 6.8.14--15 (blueprint: lem-per-qbar-dual-recollement). -/
def Restriction {V W : PerAdic.Base k} (h : V.scheme ⟶ W.scheme) : Prop :=
  (∀ n : ℤ, Nonempty (pull l hk.out Ω h ⋙ cohomology l Ω V n ≅
    cohomology l Ω W n ⋙ pull l hk.out Ω h)) ∧
  ∀ (A : Type u) [Field A] [IsAlgClosed A] (x : Spec (.of A) ⟶ V.scheme),
    ∃ (FV : generalAlgebraicallyClosedConstructibleCategory l Ω V.scheme ⥤
          ModuleCat.{max (u + 1) v} Ω)
      (FW : generalAlgebraicallyClosedConstructibleCategory l Ω W.scheme ⥤
          ModuleCat.{max (u + 1) v} Ω),
      SfAdicCommonFiberSpec l V.scheme x Ω FV ∧
      SfAdicCommonFiberSpec l W.scheme (x ≫ h) Ω FW ∧
      Nonempty (pull l hk.out Ω h ⋙ FV ≅ FW)

section Pair
variable (X Z U : PerAdic.Base k)
  (i : Z.scheme ⟶ X.scheme) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
  (j : U.scheme ⟶ X.scheme) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]

/-- Dual restriction comparisons, with the literal exceptional functor as closed target.
Source: Bhatt--Scholze 6.7.19--20 (blueprint: lem-per-qbar-dual-recollement). -/
structure DualRestrictions where
  openIso : dual l Ω B X ⋙ pull l hk.out Ω j ≅ (pull l hk.out Ω j).op ⋙ dual l Ω B U
  closedIso : dual l Ω B X ⋙ pull l hk.out Ω i ≅
    (exceptional l Ω B i).op ⋙ dual l Ω B Z

/-- Restriction uses the existing representative-normalized completed pullback shift.
Source: Bhatt--Scholze 6.7.2, 6.8.14 (blueprint: lem-per-qbar-dual-recollement). -/
@[instance_reducible] def restrictionShift {V W : PerAdic.Base k} (h : V.scheme ⟶ W.scheme) :
    (pull l hk.out Ω h).CommShift ℤ :=
  @fieldCommonPullShift l _ Ω _ _ _ V.scheme W.scheme h
    (residueInvertibleWithUnit l hk.out V.scheme)
    (residueInvertibleWithUnit l hk.out W.scheme)

/-- The exceptional shift is the literal composite of the pinned two dual shifts and
completed inverse-image shift. Contravariance uses the inverse of the inner composite;
the final equality removes the double negation of the shift index.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-dual-recollement). -/
def exceptionalShift
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme) (n : ℤ) :
    (exceptional l Ω B i).obj (K⟦n⟧) ≅ ((exceptional l Ω B i).obj K)⟦n⟧ :=
  (dual l Ω B Z).mapIso
      (((pull l hk.out Ω i).mapIso
          (dualShift l hk.out Ω X.scheme (B X).closedY
            ((B X).omegaY l hk.out Ω) K n) ≪≫
        ((restrictionShift l Ω i).commShiftIso (-n)).app
          ((dual l Ω B X).obj (op K))).symm.op) ≪≫
    dualShift l hk.out Ω Z.scheme (B Z).closedY ((B Z).omegaY l hk.out Ω)
      ((pull l hk.out Ω i).obj ((dual l Ω B X).obj (op K))) (-n) ≪≫
    eqToIso (congrArg (fun m : ℤ ↦ ((exceptional l Ω B i).obj K)⟦m⟧) (neg_neg n))

/-- The comparison squares with the actual signed dual and inverse-image shifts.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-dual-recollement). -/
def ShiftCompatible (e : DualRestrictions l Ω B X Z U i j) : Prop :=
    (∀ (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme) (n : ℤ),
      (pull l hk.out Ω j).map
          (dualShift l hk.out Ω X.scheme (B X).closedY
            ((B X).omegaY l hk.out Ω) K n).hom ≫
        ((restrictionShift l Ω j).commShiftIso (-n)).hom.app ((dual l Ω B X).obj (op K)) ≫
        (shiftFunctor _ (-n)).map (e.openIso.hom.app (op K)) =
      e.openIso.hom.app (op (K⟦n⟧)) ≫
        (dual l Ω B U).map (((restrictionShift l Ω j).commShiftIso n).inv.app K).op ≫
        (dualShift l hk.out Ω U.scheme (B U).closedY
          ((B U).omegaY l hk.out Ω) ((pull l hk.out Ω j).obj K) n).hom) ∧
    (∀ (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme) (n : ℤ),
      (pull l hk.out Ω i).map
          (dualShift l hk.out Ω X.scheme (B X).closedY
            ((B X).omegaY l hk.out Ω) K n).hom ≫
        ((restrictionShift l Ω i).commShiftIso (-n)).hom.app ((dual l Ω B X).obj (op K)) ≫
        (shiftFunctor _ (-n)).map (e.closedIso.hom.app (op K)) =
      e.closedIso.hom.app (op (K⟦n⟧)) ≫
        (dual l Ω B Z).map (exceptionalShift l Ω B X Z i K n).inv.op ≫
        (dualShift l hk.out Ω Z.scheme (B Z).closedY
          ((B Z).omegaY l hk.out Ω) ((exceptional l Ω B i).obj K) n).hom)

/-- At every finite coefficient stage the open comparison is the same comparison.
Both sides use the canonical pullback inclusion and trace-normalized dual inclusion.
Source: Bhatt--Scholze 6.8.14--15 (blueprint: lem-per-qbar-dual-recollement). -/
def OpenScalarCompatible (e : DualRestrictions l Ω B X Z U i j) : Prop :=
  ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ eE : rationalDual l Ω B P X E ⋙
          Rational.pull l hk.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) j ≅
        (Rational.pull l hk.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) j).op ⋙
          rationalDual l Ω B P U E,
      ∀ K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X.scheme E,
        (pullInclusion l hk.out Ω E j ((rationalDual l Ω B P X E).obj (op K))).hom ≫
          (pull l hk.out Ω j).map (dualInclusion l Ω B P X E K).hom ≫
          e.openIso.hom.app (op ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K)) =
        (GeneralAlgebraicallyClosedCoefficients.inclusion E).map (eE.hom.app (op K)) ≫
          (dualInclusion l Ω B P U E
            ((Rational.pull l hk.out
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) j).obj K)).hom ≫
          (dual l Ω B U).map (pullInclusion l hk.out Ω E j K).inv.op

/-- Rational exceptional restriction uses the same two rational internal-Hom duals.
Source: Bhatt--Scholze 6.7.19--20, 6.8.14 (blueprint: lem-per-qbar-dual-recollement). -/
def rationalExceptional (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω X.scheme E ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z.scheme E :=
  (rationalDual l Ω B P X E).rightOp ⋙
    (Rational.pull l hk.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) i).op ⋙
    rationalDual l Ω B P Z E

/-- The exceptional inclusion is the composite of the three prescribed comparisons.
Source: Bhatt--Scholze 6.8.14--15 (blueprint: lem-per-qbar-dual-recollement). -/
def exceptionalInclusion (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X.scheme E) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((rationalExceptional l Ω B P X Z i E).obj K) ≅
      (exceptional l Ω B i).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K) :=
  dualInclusion l Ω B P Z E
      ((Rational.pull l hk.out
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) i).obj
          ((rationalDual l Ω B P X E).obj (op K))) ≪≫
    (dual l Ω B Z).mapIso
      ((pullInclusion l hk.out Ω E i ((rationalDual l Ω B P X E).obj (op K))).symm.op) ≪≫
    (dual l Ω B Z).mapIso
      (((pull l hk.out Ω i).mapIso (dualInclusion l Ω B P X E K)).symm.op)

/-- The closed comparison commutes with every finite-stage inclusion as well.
Source: Bhatt--Scholze 6.8.14--15 (blueprint: lem-per-qbar-dual-recollement). -/
def ClosedScalarCompatible (e : DualRestrictions l Ω B X Z U i j) : Prop :=
  ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ eE : rationalDual l Ω B P X E ⋙
          Rational.pull l hk.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) i ≅
        (rationalExceptional l Ω B P X Z i E).op ⋙ rationalDual l Ω B P Z E,
      ∀ K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X.scheme E,
        (pullInclusion l hk.out Ω E i ((rationalDual l Ω B P X E).obj (op K))).hom ≫
          (pull l hk.out Ω i).map (dualInclusion l Ω B P X E K).hom ≫
          e.closedIso.hom.app
            (op ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K)) =
        (GeneralAlgebraicallyClosedCoefficients.inclusion E).map (eE.hom.app (op K)) ≫
          (dualInclusion l Ω B P Z E ((rationalExceptional l Ω B P X Z i E).obj K)).hom ≫
          (dual l Ω B Z).map (exceptionalInclusion l Ω B P X Z i E K).inv.op

/-- All six functors and all four adjunction maps on the specified constructible categories.
Source: Bhatt--Scholze 6.7.2--20, 6.8.14--15
(blueprint: lem-per-qbar-dual-recollement). -/
structure Conclusion where
  compactOpen : ∃ S : SfCompactSupportCoefficientAction l k hk.out Ω
      (Compactification.ofIsOpenImmersion j),
    Nonempty (openExtension l hk.out Ω j ≅ S.system.functor)
  compactClosed : ∃ S : SfCompactSupportCoefficientAction l k hk.out Ω
      (Compactification.ofIsProper i),
    Nonempty (arbitraryFieldDerivedPushWithUnit l hk.out Ω i ≅ S.system.functor)
  exceptionalAdjunction : arbitraryFieldDerivedPushWithUnit l hk.out Ω i ⊣ exceptional l Ω B i
  exactOpenExtension : Exact l Ω (openExtension l hk.out Ω j)
  exactOpenPull : Exact l Ω (pull l hk.out Ω j)
  exactOpenPush : Exact l Ω (arbitraryFieldDerivedPushWithUnit l hk.out Ω j)
  exactClosedPull : Exact l Ω (pull l hk.out Ω i)
  exactClosedPush : Exact l Ω (arbitraryFieldDerivedPushWithUnit l hk.out Ω i)
  exactExceptional : Exact l Ω (exceptional l Ω B i)
  openUnit (L : generalAlgebraicallyClosedConstructibleCategory l Ω U.scheme) :
    IsIso ((openAdjunction l hk.out Ω j).unit.app L)
  openCounit (L : generalAlgebraicallyClosedConstructibleCategory l Ω U.scheme) :
    IsIso ((ordinaryAdjunction l hk.out Ω j).counit.app L)
  closedCounit (L : generalAlgebraicallyClosedConstructibleCategory l Ω Z.scheme) :
    IsIso ((ordinaryAdjunction l hk.out Ω i).counit.app L)
  exceptionalUnit (L : generalAlgebraicallyClosedConstructibleCategory l Ω Z.scheme) :
    IsIso (exceptionalAdjunction.unit.app L)
  openClosedZero (L : generalAlgebraicallyClosedConstructibleCategory l Ω Z.scheme) :
    IsZero ((pull l hk.out Ω j).obj ((arbitraryFieldDerivedPushWithUnit l hk.out Ω i).obj L))
  closedOpenZero (L : generalAlgebraicallyClosedConstructibleCategory l Ω U.scheme) :
    IsZero ((pull l hk.out Ω i).obj ((openExtension l hk.out Ω j).obj L))
  exceptionalOpenZero (L : generalAlgebraicallyClosedConstructibleCategory l Ω U.scheme) :
    IsZero ((exceptional l Ω B i).obj ((arbitraryFieldDerivedPushWithUnit l hk.out Ω j).obj L))
  firstTriangle (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme) :
    ∃ δ : (arbitraryFieldDerivedPushWithUnit l hk.out Ω i).obj
          ((pull l hk.out Ω i).obj K) ⟶
        ((openExtension l hk.out Ω j).obj ((pull l hk.out Ω j).obj K))⟦(1 : ℤ)⟧,
      Triangle.mk ((openAdjunction l hk.out Ω j).counit.app K)
        ((ordinaryAdjunction l hk.out Ω i).unit.app K) δ ∈ distTriang _
  secondTriangle (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme) :
    ∃ δ : (arbitraryFieldDerivedPushWithUnit l hk.out Ω j).obj
          ((pull l hk.out Ω j).obj K) ⟶
        ((arbitraryFieldDerivedPushWithUnit l hk.out Ω i).obj
          ((exceptional l Ω B i).obj K))⟦(1 : ℤ)⟧,
      Triangle.mk (exceptionalAdjunction.counit.app K)
        ((ordinaryAdjunction l hk.out Ω j).unit.app K) δ ∈ distTriang _
  dualRestrictions : DualRestrictions l Ω B X Z U i j
  shifts : ShiftCompatible l Ω B X Z U i j dualRestrictions
  openScalars : OpenScalarCompatible l Ω B P X Z U i j dualRestrictions
  closedScalars : ClosedScalarCompatible l Ω B P X Z U i j dualRestrictions
  closedRestriction : Restriction l Ω i
  openRestriction : Restriction l Ω j

end Pair

/-- Open/closed recollement on the exact raw common-stage categories.
Source: Bhatt--Scholze 6.7.2, 6.7.7, 6.7.19--20, 6.8.14--15
(blueprint: lem-per-qbar-dual-recollement).
Proof: (1) Finite type over a field gives Noetherian finite-dimensional X, Z and U;
immersions are separated and finite type. Compare completed immersion pullback with
ordinary exact inverse image. (2) Apply ringed open/closed recollement degreewise,
then descend exact functors, their adjunctions and identities through the homotopy
and quasi-isomorphism localizations. (3) Choose the trivial open and closed
compactifications. Extension by zero commutes with sequential derived limits;
closed image preserves products. Their Roos reconstructions are therefore exactly
the specified compact-support and ordinary adic images, including tower maps.
(4) The degreewise short exact sequence gives the first triangle with its unit and
counit. All vertices are integral constructible by the stratified-perfect criterion.
(5) Rationalize Hom bijections and descend to common stages using the scalar unit
and tower equations. The units, counits, triangles and four sheaf identities descend.
(6) Ordinary adjunction and arbitrary-field evaluation duality give Ri* adjoint to
D_Z i* D_X. The natural Hom chain using open exchange gives j*D_X = D_U j*;
biduality gives i*D_X = D_Z i!. (7) The open unit and closed counit are invertible
by full faithfulness. Duality gives full faithfulness of Rj* and hence its counit
is invertible; likewise the exceptional unit is invertible. The zero composites
follow from the sheaf identities and duality. (8) Dualize the first triangle for
D_X K and use the evaluation bidual maps to obtain the second triangle with exactly
the ordinary unit and exceptional counit. (9) Signed shift comparisons preserve the
mate formulas. Finite coefficient extension preserves their evaluation, trace,
unit and counit normalizations, so the same formulas commute with every coefficient
inclusion, including the identity and towers. (10) Exact inverse image commutes with
standard truncations and cohomology. The normalized finite-level geometric stalk
comparison, inverse limit, rationalization and coefficient extension give precisely
the restricted geometric fibres. No perfectness or Galois dimension bound is used. -/
theorem qbar_dual_recollement (X Z U : PerAdic.Base k)
    (i : Z.scheme ⟶ X.scheme) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : U.scheme ⟶ X.scheme) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hc : Set.range j = (Set.range i)ᶜ) :
    ∃ (B : ∀ W : PerAdic.Base k, Datum l hk.out Ω (𝟙 W.scheme))
      (P : ∀ W : PerAdic.Base k, Properties l hk.out Ω (B W)),
      Nonempty (Conclusion l Ω B P X Z U i j) := by
  sorry

end WeilConjectures.QbarDualRecollement
