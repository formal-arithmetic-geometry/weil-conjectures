/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.NumberTheory.Padics.PadicIntegersIntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemBrownConstruction
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemEvaluationBound
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemQuotientNormalization
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientTransportInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjection
import WeilConjectures.NumberTheory.Padics.LocalFieldCoefficientStages
import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeExtensionLeftExact
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleExactCoefficientTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeProjectionAssembly
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeMateAtLevel
/-!
# The strict étale coefficient-system adjoint
Source: Zheng, Six Operations and Lefschetz--Verdier, Constructions 5.14--5.15,
Lemmas 5.16 and 5.22, and Proposition 5.24 (blueprint:
lem-pur-etale-coefficient-system-adjoint).
The structure records the actual compact-support system functor, its right adjoint,
the finite-level adjunctions, and the asserted coefficient-system coherences.
* `StrictEtaleCompactSupport` specifies the ordinary and unbounded derived functors.
* `StrictEtaleExceptionalAdjoint` records the exact linear adjoint and finite-level mates.
* `StrictEtaleExceptionalTransport` specifies the scalar and cofinal comparison maps.
* `etaleCoefficientSystemAdjoint` and its scalar/cofinal companions assert existence.
* The identity/composition theorems state coherence with canonical tensor identifications.
This core module holds the exceptional-adjoint and transport records, the integer-ring
and coefficient-change definitions, the scalar transport projection
`strictEtaleScalarTransportProjection` (blueprint: lem-pur-etale-scalar-transport-projection)
and the identity/composition theorems; `WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientSystemAdjoint` re-exports
it and proves the existence theorems (split for the per-file compile limit).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option linter.all false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
open SheafOfModules
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local irreducible] CategoryTheory.constantSheaf SheafOfModules.siteCoefficientTensor
  SheafOfModules.siteCoefficientTensorAdj
set_option backward.defeqAttrib.useBackward true
private instance strictCoefficientTensorAdditive (T : Scheme.{u})
    (O : Type (u + 1)) [CommRing O] (ell : O) {m n : ℕ} (h : n ≤ m) :
    (coefficientTensor (J := T.smallEtaleTopology) (O := O) (ell := ell) h).Additive :=
  siteCoefficientTensor_additive.{u + 1, u, u + 1}
    (coefficientQuotientMap (J := T.smallEtaleTopology) O ell h)

private instance strictCoefficientRestrictionAdditive (T : Scheme.{u})
    (O : Type (u + 1)) [CommRing O] (ell : O) {m n : ℕ} (h : n ≤ m) :
    (coefficientRestriction (J := T.smallEtaleTopology) O ell h).Additive :=
  inferInstance

/-- Use the recorded proper inverse-image additive witness at the strict site sizes.
Source: Zheng, Construction 4.1 and Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
theorem strictEtaleProperInverseAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :
    (S.val.properImage.lift n).modules.Additive := S.val.properImage.inverseAdditive n

/-- Use the recorded proper direct-image additive witness at the strict site sizes.
Source: Zheng, Construction 4.1 and Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
theorem strictEtaleProperDirectAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :
    (S.val.properImage.right n).Additive := S.val.properImage.rightAdditive n

attribute [local instance 9000] strictEtaleProperInverseAdditive strictEtaleProperDirectAdditive

section TransportTypes
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.coefficientQuotientSheaf
  SheafOfModules.coefficientQuotientMap CategoryTheory.sheafCompose
section FixedCoefficients
variable (O : Type (u + 1)) [CommRing O] (ell : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
/-- The right adjoint with actual evaluated units, counits, and transition mates.
The isomorphisms are uniquely characterized by the two adjunction equations. Quotient
coefficient maps use the recorded universal derived tensor, including nonflat quotients.
Source: Zheng, Lemmas 5.16 and 5.22, Proposition 5.24, and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleExceptionalAdjointData (S : StrictEtaleCompactSupport O ell c) where
  right : DerivedCategory (strictEtaleCoefficientSystem Y O ell) ⥤
    DerivedCategory (strictEtaleCoefficientSystem X O ell)
  [rightAdditive : right.Additive]
  [shift : right.CommShift ℤ]
  adjunction : S.functor ⊣ right
  scalarX : StrictEtaleScalarAction X O ell
  scalarY : StrictEtaleScalarAction Y O ell
  levelRight : ∀ n, DerivedCategory (strictEtaleLevel Y O ell n) ⥤
    DerivedCategory (strictEtaleLevel X O ell n)
  levelAdjunction : ∀ n, S.levelFunctor n ⊣ levelRight n
  evaluation : ∀ n, right ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ levelRight n
  quotientOpen : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).derived ⋙ S.levelDerivedOpen n ≅
      S.levelDerivedOpen m ⋙ (S.PZ.scalar h).derived
  quotientProper : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PZ.scalar h).derived ⋙ (S.properDerived.level n).direct ≅
      (S.properDerived.level m).direct ⋙ (S.PY.scalar h).derived
  quotientProjection : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).derived ⋙ S.levelFunctor n ≅
      S.levelFunctor m ⋙ (S.PY.scalar h).derived
  quotientComparison : ∀ {m n : ℕ} (h : n ≤ m),
    levelRight m ⋙ (S.PX.scalar h).derived ≅
      (S.PY.scalar h).derived ⋙ levelRight n


attribute [instance] StrictEtaleExceptionalAdjointData.rightAdditive
  StrictEtaleExceptionalAdjointData.shift

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalAdjointCoherence (S : StrictEtaleCompactSupport O ell c)
    (record : StrictEtaleExceptionalAdjointData O ell c S) : Prop :=
    -- exact
    (record.right.IsTriangulated) ∧
    -- linear
    (∀ r M, record.right.map ((record.scalarY.derived r).app M) =
      (record.scalarX.derived r).app (record.right.obj M)) ∧
    -- counit
    (∀ n, (record.evaluation n).hom =
      (mateEquiv record.adjunction (record.levelAdjunction n)
        (.mk _ _ _ _ (S.evaluation n).inv)).natTrans) ∧
    -- quotientOpenMate
    (∀ {m n : ℕ} (h : n ≤ m),
      (mateEquiv (S.levelDerivedOpenAdjunction m) (S.levelDerivedOpenAdjunction n)
        (.mk _ _ _ _ (record.quotientOpen h).hom)).natTrans =
      (S.openDerived.derivedTensor h).inv) ∧
    -- quotientProperMate
    (∀ {m n : ℕ} (h : n ≤ m),
      (record.quotientProper h).inv =
      (mateEquiv (S.properDerived.level m).adjunction (S.properDerived.level n).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom)).natTrans) ∧
    -- quotientProjection_def
    (∀ {m n : ℕ} (h : n ≤ m), record.quotientProjection h =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (record.quotientOpen h) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (record.quotientProper h) ≪≫
          (Functor.associator _ _ _).symm) ∧
    -- quotientMate
    (∀ {m n : ℕ} (h : n ≤ m),
      (record.quotientComparison h).hom =
      (mateEquiv (record.levelAdjunction m) (record.levelAdjunction n)
        (.mk _ _ _ _ (record.quotientProjection h).hom)).natTrans) ∧
    -- quotientIdentity
    (∀ n M,
      (record.quotientComparison (Nat.le_refl n)).hom.app M ≫
        (record.levelRight n).map ((S.PY.derivedUnit n).hom.app M) =
      (S.PX.derivedUnit n).hom.app ((record.levelRight n).obj M)) ∧
    -- quotientComposition
    (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m) M,
      (S.PX.derivedAssoc h₁ h₂).hom.app ((record.levelRight l).obj M) ≫
        (record.quotientComparison (h₂.trans h₁)).hom.app M =
      (S.PX.scalar h₂).derived.map ((record.quotientComparison h₁).hom.app M) ≫
        (record.quotientComparison h₂).hom.app ((S.PY.scalar h₁).derived.obj M) ≫
        (record.levelRight n).map ((S.PY.derivedAssoc h₁ h₂).hom.app M)) ∧
    -- transition
    (∀ {m n : ℕ} (h : n ≤ m) M,
      (S.PX.scalar h).derived.map ((record.evaluation m).hom.app M) ≫
        (record.quotientComparison h).hom.app ((S.PY.evaluation m).obj M) ≫
        (record.levelRight n).map
          (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm ((S.PY.transition h).app M)) =
      ((S.PX.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PX.transition h).app (record.right.obj M)) ≫ (record.evaluation n).hom.app M) ∧
    -- bound
    (∃ c_f : ℕ, ∀ (a : ℤ) M, M.IsGE a → (record.right.obj M).IsGE (a - c_f)) ∧
    -- normalized
    (∀ M, (∃ a : ℤ, M.IsGE a) →
      IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
        (J := Y.smallEtaleTopology) O ell S.PY M →
        (∃ a : ℤ, (record.right.obj M).IsGE a) ∧
          IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
            (J := X.smallEtaleTopology) O ell S.PX (record.right.obj M))

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalAdjoint (S : StrictEtaleCompactSupport O ell c) :=
  { record : StrictEtaleExceptionalAdjointData O ell c S //
    StrictEtaleExceptionalAdjointCoherence O ell c S record }

section
variable (S : StrictEtaleCompactSupport O ell c)
variable {O ell c S}

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.right (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.right



/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.adjunction
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.adjunction



/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.levelRight
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.levelRight

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.levelAdjunction
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.levelAdjunction

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.evaluation
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.evaluation




/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.quotientComparison
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  fun {m n : ℕ} (h : n ≤ m) ↦ record.val.quotientComparison h


end

end FixedCoefficients
section Transport
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  (a : StrictEtaleCoefficientChange O O' ell mu phi index)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
  (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
  (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
  (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
variable (GA : StrictEtaleExceptionalAdjoint O ell c SA)
  (GB : StrictEtaleExceptionalAdjoint O' mu c SB)
/-- The actual exceptional coefficient comparison. Its transpose is the inverse
compact-support projection followed by the extended counit. Evaluations identify it
with the identical finite-level transpose, including every quotient transition.
Source: Zheng, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleExceptionalTransportData where
  compact : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ
  right : GA.right ⋙ TX.derived ≅ TY.derived ⋙ GB.right
  levelProjection : ∀ n, SA.levelFunctor (index n) ⋙ (TY.level n).derived ≅
    (TX.level n).derived ⋙ SB.levelFunctor n
  levelRight : ∀ n, GA.levelRight (index n) ⋙ (TX.level n).derived ≅
    (TY.level n).derived ⋙ GB.levelRight n
  quotientX : StrictEtaleTransportQuotient TX
  quotientY : StrictEtaleTransportQuotient TY


/-- The specified data and canonical coherence of `StrictEtaleExceptionalTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalTransportCoherence
    (record : StrictEtaleExceptionalTransportData a c SA SB TX TY TZ GA GB) : Prop :=
    -- mate
    (record.right.hom = (mateEquiv GA.adjunction GB.adjunction
      (.mk _ _ _ _ record.compact.projection.inv)).natTrans) ∧
    -- projectionEvaluation
    (∀ n K,
      (TY.derivedEvaluation n).hom.app (SA.functor.obj K) ≫
        (TY.level n).derived.map ((SA.evaluation (index n)).hom.app K) ≫
        (record.levelProjection n).hom.app ((SA.PX.evaluation (index n)).obj K) =
      (SB.PY.evaluation n).map (record.compact.projection.hom.app K) ≫
        (SB.evaluation n).hom.app (TX.derived.obj K) ≫
        (SB.levelFunctor n).map ((TX.derivedEvaluation n).hom.app K)) ∧
    -- levelMate
    (∀ n, (record.levelRight n).hom =
      (mateEquiv (GA.levelAdjunction (index n)) (GB.levelAdjunction n)
        (.mk _ _ _ _ (record.levelProjection n).inv)).natTrans) ∧
    -- quotient
    (∀ {m n : ℕ} (h : n ≤ m) M,
      (SB.PX.scalar h).derived.map ((record.levelRight m).hom.app M) ≫
        (GB.quotientComparison h).hom.app ((TY.level m).derived.obj M) ≫
        (GB.levelRight n).map ((record.quotientY.derived h).inv.app M) =
      (record.quotientX.derived h).inv.app ((GA.levelRight (index m)).obj M) ≫
        (TX.level n).derived.map ((GA.quotientComparison (index.monotone h)).hom.app M) ≫
        (record.levelRight n).hom.app ((SA.PY.scalar (index.monotone h)).derived.obj M)) ∧
    -- rightEvaluation
    (∀ n M,
      (TX.derivedEvaluation n).hom.app (GA.right.obj M) ≫
        (TX.level n).derived.map ((GA.evaluation (index n)).hom.app M) ≫
        (record.levelRight n).hom.app ((SA.PY.evaluation (index n)).obj M) =
      (SB.PX.evaluation n).map (record.right.hom.app M) ≫
        (GB.evaluation n).hom.app (TY.derived.obj M) ≫
        (GB.levelRight n).map ((TY.derivedEvaluation n).hom.app M))

/-- The specified data and canonical coherence of `StrictEtaleExceptionalTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalTransport :=
  { record : StrictEtaleExceptionalTransportData a c SA SB TX TY TZ GA GB //
    StrictEtaleExceptionalTransportCoherence a c SA SB TX TY TZ GA GB record }

section
variable {a c SA SB TX TY TZ GA GB}


/-- The specified data and canonical coherence of `StrictEtaleExceptionalTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalTransport.right
    (record : StrictEtaleExceptionalTransport a c SA SB TX TY TZ GA GB) :=
  record.val.right






end

end Transport
end TransportTypes
section EfficientRealization
set_option backward.isDefEq.respectTransparency.types true
section IntegerMaps
variable (l : ℕ) [Fact l.Prime]
  {E F : Type (u + 1)} [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
/-- A finite p-adic field embedding preserves the recorded integer rings.
Source: Zheng, coefficient change in Proposition 2.29(2); Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: uniqueness of the extending absolute value identifies the two absolute values
on E. The integer rings are their unit balls, so the embedding preserves membership. -/
theorem strictEtaleIntegerMap_mem (i : E →ₐ[Padic l] F)
    (x : Padic.coefficientExtensionIntegers l E) :
    i (x : E) ∈ Padic.coefficientExtensionIntegers l F := by
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hF := (Padic.extension_integers_dvr l F
    (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := Padic l) (L := F))).choose_spec.choose_spec
  apply (hF.1 _).mpr
  change spectralNorm (Padic l) F (i (x : E)) ≤ 1
  have hmap : spectralNorm (Padic l) F (i (x : E)) =
      spectralNorm (Padic l) E (x : E) := by
    unfold spectralNorm
    rw [minpoly.algHom_eq i i.injective]
  rw [hmap]
  exact (hE.1 _).mp x.property
/-- Restrict the actual field embedding to the integer rings.
Source: Zheng, Proposition 2.29(2); Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleIntegerMap (i : E →ₐ[Padic l] F) :
    Padic.coefficientExtensionIntegers l E →+* Padic.coefficientExtensionIntegers l F :=
  (i.toRingHom.comp (Padic.coefficientExtensionIntegers l E).subtype).codRestrict
    (Padic.coefficientExtensionIntegers l F) (strictEtaleIntegerMap_mem l i)
end IntegerMaps
/-- Change coefficients at unchanged positive indices, with the actual quotient map.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleSameIndexChange {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    (ell : O) (phi : O →+* O') :
    StrictEtaleCoefficientChange O O' ell (phi ell) phi (OrderHom.id : ℕ →o ℕ) where
  ring := strictCoefficientRingMap ell phi
  generators := fun _n _x ↦ Ideal.Quotient.lift_mk _ _ _
/-- Positive-exponent indexing of the ramified subsequence: n means e*(n+1).
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleRamifiedIndex (e : ℕ) : ℕ →o ℕ where
  toFun n := e * (n + 1) - 1
  monotone' := fun _ _ h ↦
    Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right h 1)) 1
/-- Reindex by the equal coefficient ideals, using the canonical quotient equivalences.
Source: Zheng, Construction 4.1; Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleRamifiedChange {O : Type (u + 1)} [CommRing O] (ell mu : O) (e : ℕ)
    (h : ∀ n, (Ideal.span ({ell} : Set O)) ^ (strictEtaleRamifiedIndex e n + 1) =
      (Ideal.span ({mu} : Set O)) ^ (n + 1)) :
    StrictEtaleCoefficientChange O O ell mu (RingHom.id O) (strictEtaleRamifiedIndex e) where
  ring n := (Ideal.quotEquivOfEq (h n)).toRingHom
  generators := fun n x ↦ Ideal.quotEquivOfEq_mk (h n) x
end EfficientRealization

private def scalarLevelModule {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (t : A) (phi : A →+* B) (n : ℕ) :=
  (ModuleCat.restrictScalars (strictCoefficientRingMap t phi n)).obj
    (ModuleCat.of (B ⧸ Ideal.span {phi t} ^ (n + 1))
      (B ⧸ Ideal.span {phi t} ^ (n + 1)))
private theorem scalarLevelFree
    (l : ℕ) [Fact l.Prime] {E F : Type (u + 1)} [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (n : ℕ) :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r)
      ((Padic.coefficientExtensionIntegers l E) ⧸
        (Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E))) ^ (n + 1))
      (scalarLevelModule (Padic.coefficientExtensionUniformizer l E)
        (strictEtaleIntegerMap l i) n)) := by
  classical
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionIntegers l F
  let phi : A →+* B := strictEtaleIntegerMap l i
  let : Algebra E F := i.toRingHom.toAlgebra
  let : Algebra A F := (i.toRingHom.comp A.subtype).toAlgebra
  let : Algebra A B := phi.toAlgebra
  have : IsScalarTower A E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Padic l) E F :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (i.commutes x).symm
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite (Padic l) E F
  have hA := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsFractionRing A E := hA.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing A := hA.2.2.2.2.2.2.2.2.1
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic l) E).injective
  have : IsIntegrallyClosed A := inferInstance
  have : IsNoetherianRing A := inferInstance
  have : Algebra.IsSeparable E F := inferInstance
  have : IsIntegralClosure B A F := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    change x ∈ integralClosure A F ↔ ∃ y : B, (y : F) = x
    rw [← Padic.padic_integers_integralClosure l E F i x]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : Module.IsTorsionFree A F := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    intro x y hxy
    apply Subtype.val_injective
    exact i.injective hxy
  have : Module.Finite A B := IsIntegralClosure.finite A E F B
  have : Module.Free A B := IsIntegralClosure.module_free A E F B
  let I : Ideal A := (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A)) ^
    (n + 1)
  let J : Ideal B := (Ideal.span ({phi (Padic.coefficientExtensionUniformizer l E)} : Set B)) ^
    (n + 1)
  have hJ : I.map (algebraMap A B) = J := by
    simp only [I, J, Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl
  let Q := scalarLevelModule (Padic.coefficientExtensionUniformizer l E) phi n
  let : Module (A ⧸ I) (B ⧸ J) :=
    Module.compHom (B ⧸ J) (strictCoefficientRingMap
      (Padic.coefficientExtensionUniformizer l E) phi n)
  let : Module (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := inferInstance
  let e : (B ⧸ I.map (algebraMap A B)) ≃ₗ[A ⧸ I] Q :=
    (Ideal.quotEquivOfEq hJ).toAddEquiv.toLinearEquiv (by
      intro a x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
  exact ⟨Module.finrank A B,
    ⟨((Module.finBasis A B).baseChange (A ⧸ I)).map
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv.trans e)⟩⟩

private theorem scalarNonzeroNonunit
    (l : ℕ) [Fact l.Prime] {E F : Type (u + 1)} [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) :
    strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E) ≠ 0 ∧
    ¬ IsUnit (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) := by
  let : Algebra E F := i.toRingHom.toAlgebra
  have : IsScalarTower (Padic l) E F :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (i.commutes x).symm
  have hcompat (x : E) :
      Padic.coefficientExtensionAbsoluteValue l F (algebraMap E F x) =
        Padic.coefficientExtensionAbsoluteValue l E x := by
    change spectralNorm (Padic l) F (i x) = spectralNorm (Padic l) E x
    unfold spectralNorm
    rw [minpoly.algHom_eq i i.injective]
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hF := (Padic.extension_integers_dvr l F
    (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := Padic l) (L := F))).choose_spec.choose_spec
  have : IsLocalRing (Padic.coefficientExtensionIntegers l E) := hE.2.2.2.1
  have : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) :=
    hE.2.2.2.2.2.2.2.1
  have : IsLocalRing (Padic.coefficientExtensionIntegers l F) := hF.2.2.2.1
  have : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l F) :=
    hF.2.2.2.2.2.2.2.1
  have ht : Irreducible (Padic.coefficientExtensionUniformizer l E) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      ((IsLocalRing.eq_maximalIdeal (R := Padic.coefficientExtensionIntegers l E)
          hE.2.2.2.2.1).symm.trans
        hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec.symm)
  have hv : Irreducible (Padic.coefficientExtensionUniformizer l F) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      ((IsLocalRing.eq_maximalIdeal (R := Padic.coefficientExtensionIntegers l F)
          hF.2.2.2.2.1).symm.trans
        hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec.symm)
  obtain ⟨j, hj, _, _, e, w, he, hp, _⟩ :=
    Padic.local_field_coefficient_stages l E F hcompat
      (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l F)
      hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hj' : j = strictEtaleIntegerMap l i := by
    apply RingHom.ext
    intro x
    apply Subtype.val_injective
    exact hj x
  rw [hj'] at hp
  constructor
  · intro hz
    apply ht.ne_zero
    apply Subtype.val_injective
    apply i.injective
    have hz' := congrArg (fun y : Padic.coefficientExtensionIntegers l F ↦ (y : F)) hz
    change i (Padic.coefficientExtensionUniformizer l E : E) = 0 at hz'
    change i (Padic.coefficientExtensionUniformizer l E : E) = i (0 : E)
    exact hz'.trans i.map_zero.symm
  · rw [hp]
    intro h
    have hpow := isUnit_of_mul_isUnit_right h
    exact hv.not_isUnit ((isUnit_pow_iff (by omega : e ≠ 0)).mp hpow)

private theorem scalarTensor_exact
    (l : ℕ) [Fact l.Prime] {E F : Type (u + 1)} [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (siteCoefficientTensor.{u + 1, u, u + 1}
      ((strictEtaleSameIndexChange (Padic.coefficientExtensionUniformizer l E)
        (strictEtaleIntegerMap l i)).sheaf T n)) := by
  let t := Padic.coefficientExtensionUniformizer l E
  let phi := strictEtaleIntegerMap l i
  let A := Padic.coefficientExtensionIntegers l E ⧸ Ideal.span {t} ^ (n + 1)
  let B := Padic.coefficientExtensionIntegers l F ⧸ Ideal.span {phi t} ^ (n + 1)
  let : Algebra A B := (strictCoefficientRingMap t phi n).toAlgebra
  obtain ⟨r, ⟨b⟩⟩ := scalarLevelFree l i n
  change Module.Basis (Fin r) A B at b
  let : Module.Free A B := Module.Free.of_basis b
  let : Module.Finite A B := Module.Finite.of_basis b
  let α := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (algebraMap A B))
  change PreservesFiniteLimits (siteCoefficientTensor.{u + 1, u, u + 1} α)
  apply constantFiniteFree_extensionLeftExact T.smallEtaleTopology
    (CommRingCat.of A) (CommRingCat.of B)
    (siteCoefficientTensor.{u + 1, u, u + 1} α) (fun _ ↦ by
      unfold siteCoefficientTensor
      rfl)
  intro M N f
  unfold siteCoefficientTensor
  change changeOfRingsHom α M f = 𝟙 _ ≫ changeOfRingsHom α M f ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

section ScalarTargetAssembly
private theorem brownEvaluation_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {E : A ⥤ C} {F : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (s : L ⋙ F ≅ E ⋙ L') (t : R ⋙ E ≅ F ⋙ R')
    (h : ∀ M, L'.map (t.hom.app M) ≫ adj'.counit.app (F.obj M) =
      s.inv.app (R.obj M) ≫ F.map (adj.counit.app M)) :
    t.hom = (mateEquiv adj adj' (.mk _ _ _ _ s.inv)).natTrans := by
  ext M
  apply (adj'.homEquiv _ _).symm.injective
  exact (h M).trans (mateEquiv_counit adj adj' (.mk _ _ _ _ s.inv) M).symm

private def brownConstantUnderlying (T : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    Etale.SystemProjection.constantModule T A ⋙
      sheafCompose T.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A)
        AddCommGrpCat.{u + 1}) ≅
      SheafOfModules.toSheaf.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj A)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext U x; rfl)

private theorem brownConstant_exact (T : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    PreservesFiniteLimits (Etale.SystemProjection.constantModule T A) ∧
      PreservesFiniteColimits (Etale.SystemProjection.constantModule T A) := by
  let F := Etale.SystemProjection.constantModule T A
  let V := sheafCompose T.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  have : PreservesFiniteLimits (F ⋙ V) :=
    preservesFiniteLimits_of_natIso (brownConstantUnderlying T A).symm
  have : PreservesFiniteColimits (F ⋙ V) :=
    preservesFiniteColimits_of_natIso (brownConstantUnderlying T A).symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F V,
    preservesFiniteColimits_of_reflects_of_preserves F V⟩

private theorem brownConstant_faithful (T : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (Etale.SystemProjection.constantModule T A).Faithful where
  map_injective {M N} {f g} h := by
    ext U x
    exact congrArg (fun k ↦ k.hom.app U x) h

private theorem brownRealization_isLE_iff
    {O : Type (u + 1)} [CommRing O] {t : O} {T : Scheme.{u}}
    {P : StrictEtaleEvaluation T O t} (R : StrictEtaleBrownRealization O t T P)
    (n : ℕ) (K : DerivedCategory (strictEtaleLevel T O t n)) (b : ℤ) :
    ((R.derived n).obj K).IsLE b ↔ K.IsLE b := by
  let := strictEtaleLevelDerived T O t n
  let F : strictEtaleLevel T O t n ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) :=
    strictEtaleBrownConstant O t T n
  have : F.Additive := R.val.ordinaryAdditive n
  have : PreservesFiniteLimits F :=
    (brownConstant_exact T (.of (strictEtaleBrownRing O t n))).1
  have : PreservesFiniteColimits F :=
    (brownConstant_exact T (.of (strictEtaleBrownRing O t n))).2
  have : F.Faithful := brownConstant_faithful T (.of (strictEtaleBrownRing O t n))
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel T O t n) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) (R.derived n) := ⟨R.factors n⟩
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel T O t n) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors⟩
  let e : R.derived n ≅ F.mapDerivedCategory := Localization.liftNatIso
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (R.derived n) F.mapDerivedCategory (Iso.refl _)
  constructor
  · intro h
    have := h
    have hm := DerivedCategory.TStructure.t.isLE_of_iso (e.app K) b
    apply (DerivedCategory.isLE_iff K b).mpr
    intro i hi
    exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isLE_iff _ b).mp hm i hi)
  · intro h
    have := h
    have := F.isLE_mapDerivedCategory_obj K b
    exact DerivedCategory.TStructure.t.isLE_of_iso (e.app K).symm b

private theorem brownFiniteAmplitude
    (k : Type u) [Field k] [IsAlgClosed k] (p l : ℕ) [Fact p.Prime] [Fact l.Prime]
    [CharP k p] (hl : l ≠ p)
    {X Y : Scheme.{u}} (xk : X ⟶ Spec (.of k)) (yk : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType xk] [LocallyOfFiniteType yk]
    [QuasiCompact xk] [QuasiCompact yk]
    (f : X ⟶ Y) (hf : f ≫ yk = xk)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ N : ℕ, ∀ (c : Compactification f) (A : Type (u + 1)) [CommRing A] [Finite A],
      (∃ r : ℕ, (l : A) ^ r = 0) →
      ∀ (b : ℤ) (K : Etale.DerivedCategoryModule A X), K.IsLE b →
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj K).IsLE (b + (N : ℤ)) := by
  obtain ⟨N, hN⟩ := Etale.exceptionalConstantTensor k p l hl xk yk f hf
  refine ⟨N, fun c A _ _ ht ↦ (hN c A ?_).1⟩
  obtain ⟨r, hr⟩ := ht
  exact ⟨r, fun z ↦ by rw [hr, zero_mul]⟩

private theorem brownFiniteQuotient
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ha : ∃ r : ℕ, (l : A) ^ r = 0) (hb : ∃ r : ℕ, (l : B) ^ r = 0)
    (a : A →+* B)
    (ga : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (gb : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X)
    (aa : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ ga)
    (ab : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ gb) :
    ∃ q : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.scalarExtension a Y ≅ Etale.scalarExtension a X ⋙
          Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c,
      q.hom = Etale.compactScalarMap a c ∧
        IsIso (mateEquiv aa ab (.mk _ _ _ _ q.inv)).natTrans := by
  obtain ⟨q, hq, r, _, rho, _, _, b, hb, _⟩ :=
    Etale.etaleCoefficientQuotientNormalization D l hl f c A B
      (by simpa only [Nat.cast_pow] using ha)
      (by simpa only [Nat.cast_pow] using hb) a ga gb aa ab
  refine ⟨q, hq, ?_⟩
  change IsIso (Etale.etaleCoefficientQuotientMate a c aa ab q)
  rw [← hb]
  infer_instance

private theorem brownInverseWord {C : Type*} [Category C]
    {V₀ V₁ V₂ V₃ V₄ V₅ : C}
    (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₂) (c : V₂ ≅ V₃)
    (d : V₃ ≅ V₄) (e : V₄ ≅ V₅) (q : V₀ ≅ V₅)
    (h : a ≫ b ≫ c.hom ≫ d.hom ≫ e.hom = q.hom) :
    e.inv ≫ d.inv ≫ c.inv = q.inv ≫ a ≫ b := by
  apply (cancel_epi q.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id,
    Iso.hom_inv_id]

private theorem brownCubeMate_isIso
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    [c.ReflectsIsomorphisms]
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (hF : IsIso (mateEquiv adj adj' (.mk _ _ _ _ pF.inv)).natTrans)
    (hK : IsIso (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).natTrans)
    (hθ : IsIso (mateEquiv adj' adjK' (.mk _ _ _ _ θ')).natTrans) :
    IsIso (mateEquiv adj adjK (.mk _ _ _ _ θ)).natTrans := by
  have hFapp (M : B) : IsIso ((mateEquiv adj adj'
      (.mk _ _ _ _ pF.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hKapp (M : D) : IsIso ((mateEquiv adjK adjK'
      (.mk _ _ _ _ pK.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hθapp (M : B') : IsIso ((mateEquiv adj' adjK'
      (.mk _ _ _ _ θ')).app M) := NatIso.isIso_app_of_isIso _ M
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have he := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc M
  have hi : IsIso
      (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M) ≫
        (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M)) := by
    rw [he]
    infer_instance
  have : IsIso (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M)) :=
    IsIso.of_isIso_comp_right _
      ((mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M))
  exact isIso_of_reflects_iso _ c

private theorem brownQuotientMate_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {O : Type (u + 1)} [CommRing O] {t : O}
    (S : StrictEtaleCompactSupport O t c) (B : StrictEtaleBrownConstruction O t c S)
    (hfinite : ∀ n, Finite (strictEtaleBrownRing O t n))
    (htorsion : ∀ n, ∃ r : ℕ, (l : strictEtaleBrownRing O t n) ^ r = 0)
    (g : ∀ n, DerivedCategory (strictEtaleLevel Y O t n) ⥤
      DerivedCategory (strictEtaleLevel X O t n))
    (adjN : ∀ n, S.levelFunctor n ⊣ g n) {m n : ℕ} (h : n ≤ m) :
    IsIso (strictEtaleBrownQuotientMate B adjN h) := by
  have : Finite (strictEtaleBrownRing O t m) := hfinite m
  have : Finite (strictEtaleBrownRing O t n) := hfinite n
  have := B.realizationX.val.equivalence m
  have := B.realizationY.val.equivalence m
  have := B.realizationX.val.equivalence n
  have := B.realizationY.val.equivalence n
  let Fm := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c
  let Fn := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c
  have : Fm.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
  have : Fn.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
  let am : Fm ⊣ Fm.rightAdjoint := Adjunction.ofIsLeftAdjoint Fm
  let an : Fn ⊣ Fn.rightAdjoint := Adjunction.ofIsLeftAdjoint Fn
  obtain ⟨q, hq, hib⟩ := brownFiniteQuotient D l hl f c
    (strictEtaleBrownRing O t m) (strictEtaleBrownRing O t n)
    (htorsion m) (htorsion n) (strictEtaleBrownRingMap O t h)
    Fm.rightAdjoint Fn.rightAdjoint am an
  have him := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (adjN m) am (B.realizationX.derived m) (B.realizationY.derived m)
    (B.levelComparison m).symm
  have hin := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (adjN n) an (B.realizationX.derived n) (B.realizationY.derived n)
    (B.levelComparison n).symm
  have hc (P : DerivedCategory (strictEtaleLevel X O t m)) :
      Fn.map ((B.realizationX.scalar h).inv.app P) ≫
        (B.levelComparison n).inv.app ((S.PX.scalar h).derived.obj P) ≫
        (B.realizationY.derived n).map ((B.projection h).hom.app P) =
      q.inv.app ((B.realizationX.derived m).obj P) ≫
        (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map
          ((B.levelComparison m).inv.app P) ≫
        (B.realizationY.scalar h).inv.app ((S.levelFunctor m).obj P) := by
    have he := B.projection_recorded_q h P
    rw [← hq] at he
    exact brownInverseWord _ _
      ((B.realizationY.derived n).mapIso ((B.projection h).app P)).symm
      ((B.levelComparison n).app ((S.PX.scalar h).derived.obj P))
      (Fn.mapIso ((B.realizationX.scalar h).app P))
      (q.app ((B.realizationX.derived m).obj P)) he
  exact brownCubeMate_isIso (adjN m) (adjN n) am an
    (B.realizationX.derived m) (B.realizationY.derived m)
    (B.realizationX.derived n) (B.realizationY.derived n)
    (B.levelComparison m) (B.realizationX.scalar h)
    (B.realizationY.scalar h) (B.levelComparison n)
    (B.projection h).hom q.inv hc him hin hib

private theorem scalarTargetAdjoint
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (t : Padic.coefficientExtensionIntegers l E) (htzero : t ≠ 0)
    (htunit : ¬ IsUnit t)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
      t c,
      Nonempty (StrictEtaleExceptionalAdjoint _ _ c S) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  obtain ⟨hfinite, htorsion, _, _, ⟨S⟩, hB⟩ :=
    etaleSystemBrownConstruction D l _hl E t htzero htunit f c
  obtain ⟨B⟩ := hB S
  have : B.right.Additive := B.rightAdditive
  have : B.right.CommShift ℤ := B.rightShift
  have hleft (n : ℕ) : (S.levelFunctor n).IsLeftAdjoint := by
    let : CommRing (strictEtaleBrownRing O t n) :=
      Ideal.Quotient.commRing ((Ideal.span ({t} : Set O)) ^ (n + 1))
    have : Finite (strictEtaleBrownRing O t n) := hfinite n
    have := B.realizationX.val.equivalence n
    have := B.realizationY.val.equivalence n
    have := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
      (strictEtaleBrownRing O t n) c
    have : (S.levelFunctor n ⋙ B.realizationY.derived n).IsLeftAdjoint :=
      Functor.isLeftAdjoint_of_iso (B.levelComparison n).symm
    exact (Functor.isLeftAdjoint_comp_iff_left (S.levelFunctor n)
      (B.realizationY.derived n)).mp inferInstance
  let g (n : ℕ) := @Functor.rightAdjoint _ _ _ _ (S.levelFunctor n) (hleft n)
  let adjN (n : ℕ) : S.levelFunctor n ⊣ g n :=
    @Adjunction.ofIsLeftAdjoint _ _ _ _ (S.levelFunctor n) (hleft n)
  obtain ⟨H⟩ := etaleSystemEvaluationBound D l _hl E t htzero htunit
    f c S B B.right B.adjunction g adjN
  have : Fact D.p.Prime := ⟨D.prime⟩
  let := Fintype.ofFinite D.k₀
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : CharP D.k D.p :=
    charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  obtain ⟨N, hN⟩ := brownFiniteAmplitude D.k D.p l _hl
    (X ↘ Spec (.of D.k)) (Y ↘ Spec (.of D.k)) f (comp_over f _)
  have hamp (n : ℕ) (b : ℤ) (K : DerivedCategory (strictEtaleLevel X O t n))
      (hK : K.IsLE b) : ((S.levelFunctor n).obj K).IsLE (b + (N : ℤ)) := by
    have : Finite (strictEtaleBrownRing O t n) := hfinite n
    have hb := @hN c (strictEtaleBrownRing O t n)
      (Ideal.Quotient.commRing ((Ideal.span ({t} : Set O)) ^ (n + 1))) (hfinite n)
      (htorsion n) b ((B.realizationX.derived n).obj K)
      ((brownRealization_isLE_iff B.realizationX n K b).mpr hK)
    apply (brownRealization_isLE_iff B.realizationY n _ _).mp
    exact ⟨(DerivedCategory.TStructure.t.le (b + (N : ℤ))).prop_of_iso
      ((B.levelComparison n).app K).symm hb.le⟩
  have hbound := H.lower_bound N hamp
  have hquot {m n : ℕ} (h : n ≤ m) :
      IsIso (strictEtaleBrownQuotientMate B adjN h) :=
    brownQuotientMate_isIso D l _hl f c S B hfinite htorsion g adjN h
  let data : StrictEtaleExceptionalAdjointData O t c S :=
    { right := B.right
      rightAdditive := B.rightAdditive
      shift := B.rightShift
      adjunction := B.adjunction
      scalarX := B.scalarX
      scalarY := B.scalarY
      levelRight := g
      levelAdjunction := adjN
      evaluation := H.theta
      quotientOpen := B.openProjection
      quotientProper := B.properProjection
      quotientProjection := B.projection
      quotientComparison := fun h ↦ @asIso _ _ _ _
        (strictEtaleBrownQuotientMate B adjN h) (hquot h) }
  refine ⟨S, ⟨⟨data, ?_⟩⟩⟩
  refine ⟨B.rightExact, B.rightLinear, ?_, B.openMate, B.properMate,
    B.projection_def, ?_, H.coefficient_identity, H.coefficient_composition,
    ?_, ⟨N, hbound⟩, ?_⟩
  · intro n
    exact brownEvaluation_mate B.adjunction (adjN n) (S.evaluation n)
      (H.theta n) (H.counit n)
  · intro m n h
    rfl
  · intro m n h M
    change (S.PX.scalar h).derived.map ((H.theta m).hom.app M) ≫
      (strictEtaleBrownQuotientMate B adjN h).app ((S.PY.evaluation m).obj M) ≫
      (g n).map (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PY.transition h).app M)) = _
    exact (H.transition h M).symm
  · intro M hM hnormalized
    obtain ⟨a, ha⟩ := hM
    exact ⟨⟨a - N, hbound a M ha⟩,
      etaleSystemQuotientNormalization D l _hl E t htzero htunit
        f c S B B.right B.adjunction g adjN H M hnormalized⟩
end ScalarTargetAssembly

/-- The geometric scalar-extension projection data needed by the exceptional transport.
This is the finite-free geometric stage of the scalar comparison.
Source: Zheng, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-scalar-transport-projection).
The coefficient rings at each level are finite free, so the tensor extension is exact.
The inverse-image scalar squares on tensor generators, together with their open and
proper mates, assemble to a compact-support projection.  The finite-level mate
comparison is invertible by the finite coefficient projection formula.  This statement
isolates that geometric construction from the final exceptional-adjoint transpose. -/
theorem strictEtaleScalarTransportProjection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (F : Type (u + 1)) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (i : E →ₐ[Padic l] F)
    (SA : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) c)
    (GA : StrictEtaleExceptionalAdjoint _ _ c SA) :
    let a := strictEtaleSameIndexChange (Padic.coefficientExtensionUniformizer l E)
      (strictEtaleIntegerMap l i)
    ∃ (SB : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l F)
        (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) c)
      (GB : StrictEtaleExceptionalAdjoint _ _ c SB)
      (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
      (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
      (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ),
      ∃ P : StrictEtaleTransportProjection a c SA SB TX TY TZ,
        ∀ n, IsIso (mateEquiv (GA.levelAdjunction n)
          (GB.levelAdjunction n) (.mk _ _ _ _ (P.level n).inv)).natTrans := by
  classical
  let a := strictEtaleSameIndexChange (Padic.coefficientExtensionUniformizer l E)
    (strictEtaleIntegerMap l i)
  obtain ⟨htzero, htunit⟩ := scalarNonzeroNonunit l i
  obtain ⟨SB, ⟨GB⟩⟩ := scalarTargetAdjoint D l _hl F
    (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E))
    htzero htunit f c
  obtain ⟨TX⟩ := nonempty_strictEtaleExactCoefficientTransport a SA.PX SB.PX
    (fun n ↦ scalarTensor_exact l i X n)
  obtain ⟨TY⟩ := nonempty_strictEtaleExactCoefficientTransport a SA.PY SB.PY
    (fun n ↦ scalarTensor_exact l i Y n)
  obtain ⟨TZ⟩ := nonempty_strictEtaleExactCoefficientTransport a SA.PZ SB.PZ
    (fun n ↦ scalarTensor_exact l i c.Z n)
  let hfree := fun n ↦ scalarLevelFree l i n
  obtain ⟨P⟩ := strictEtaleFiniteFreeProjectionAssembly a c SA SB TX TY TZ hfree
  exact ⟨SB, GB, TX, TY, TZ, P, fun n ↦
    strictEtaleFiniteFreeMateAtLevel a c SA SB TX TY TZ hfree P
      GA.levelRight GB.levelRight GA.levelAdjunction GB.levelAdjunction n⟩

end AlgebraicGeometry

section IdentityTransportProof
private theorem strictOrdinaryImage_additive
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {T S : AlgebraicGeometry.Scheme.{u}} {g : T ⟶ S}
    (A : AlgebraicGeometry.StrictEtaleOrdinaryImage O ell g) : A.inverse.Additive :=
  A.systemInverseAdditive

attribute [local instance 7000] strictOrdinaryImage_additive
attribute [local instance 6000]
  SheafOfModules.CoefficientSystemOrdinaryImage.systemInverseAdditive
  SheafOfModules.CoefficientSystemOrdinaryImage.inverseAdditive
set_option backward.isDefEq.respectTransparency true
universe v w
attribute [local instance 5000] AlgebraicGeometry.strictEtaleSystemDerived
  AlgebraicGeometry.strictEtaleLevelDerived
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.constantSheaf SheafOfModules.siteCoefficientTensor
  SheafOfModules.siteCoefficientTensorAdj
  SheafOfModules.coefficientQuotientMap
  AlgebraicGeometry.StrictEtaleCoefficientChange.sheaf


namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  {O : Type w} [CommRing O] {ell : O}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem systemHom_ext {M N : CoefficientSystem (J := J) O ell}
    (f g : M.Hom N) (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

private def systemIso {M N : CoefficientSystem (J := J) O ell}
    (e : ∀ n, M.level n ≅ N.level n)
    (h : ∀ n, (e (n + 1)).hom ≫ N.transition n = M.transition n ≫
      (coefficientRestriction (J := J) O ell (Nat.le_succ n)).map (e n).hom) : M ≅ N where
  hom := ⟨fun n ↦ (e n).hom, h⟩
  inv := ⟨fun n ↦ (e n).inv, fun n ↦ by
    apply (cancel_epi (e (n + 1)).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc, h]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]⟩
  hom_inv_id := systemHom_ext _ _ (fun n ↦ (e n).hom_inv_id)
  inv_hom_id := systemHom_ext _ _ (fun n ↦ (e n).inv_hom_id)
private def systemNatIso (F : CoefficientSystem (J := J) O ell ⥤
    CoefficientSystem (J := J) O ell)
    (e : ∀ n, F ⋙ coefficientEvaluation n ≅ coefficientEvaluation n)
    (h : ∀ M n, (e (n + 1)).hom.app M ≫ M.transition n =
      (F.obj M).transition n ≫
        (coefficientRestriction (J := J) O ell (Nat.le_succ n)).map ((e n).hom.app M)) :
    F ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ systemIso (fun n ↦ (e n).app M) (h M))
    (fun {_M _N} f ↦ systemHom_ext _ _ (fun n ↦ (e n).hom.naturality f))

private theorem systemNatIso_app (F : CoefficientSystem (J := J) O ell ⥤
    CoefficientSystem (J := J) O ell)
    (e : ∀ n, F ⋙ coefficientEvaluation n ≅ coefficientEvaluation n)
    (h : ∀ M n, (e (n + 1)).hom.app M ≫ M.transition n =
      (F.obj M).transition n ≫
        (coefficientRestriction (J := J) O ell (Nat.le_succ n)).map ((e n).hom.app M))
    (M : CoefficientSystem (J := J) O ell) (n : ℕ) :
    ((systemNatIso F e h).hom.app M).app n = (e n).hom.app M := rfl

end SheafOfModules

namespace CategoryTheory
private def identityDescent
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F : A ⥤ A) [F.Additive] (R : DerivedCategory A ⥤ DerivedCategory A)
    (p : DerivedCategory.Q ⋙ R ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (I : F ≅ 𝟭 A) :
    { e : R ≅ 𝟭 _ // ∀ K : CochainComplex A ℤ,
      e.hom.app (DerivedCategory.Q.obj K) = p.hom.app K ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex I (.up ℤ)).hom.app K) } := by
  let q := DerivedCategory.Q (C := A)
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let t : q ⋙ R ≅ q := p ≪≫
    isoWhiskerRight (NatIso.mapHomologicalComplex I (.up ℤ)) q ≪≫
      isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ (.up ℤ)) q ≪≫
        Functor.leftUnitor q
  letI liftR : Localization.Lifting q W q R := ⟨t⟩
  refine ⟨Localization.liftNatIso q W q q R (𝟭 _) (Iso.refl _), ?_⟩
  intro K
  change (Localization.liftNatTrans q W q q R (𝟭 _) (𝟙 q)).app (q.obj K) = _
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, liftR, NatTrans.id_app,
    Functor.rightUnitor_inv_app, Category.comp_id]
  change t.hom.app K = _
  have hid : (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app K = 𝟙 K := by
    ext n
    rfl
  dsimp only [t, q, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, Functor.leftUnitor_hom_app, hid, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc]
  erw [hid, DerivedCategory.Q.map_id]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  exact congrArg (fun f ↦ p.hom.app K ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex I (.up ℤ)).hom.app K) ≫ f)
    (Category.id_comp (𝟙 (DerivedCategory.Q.obj K))) |>.trans
      (congrArg (fun f ↦ p.hom.app K ≫ f)
        (Category.comp_id (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex I (.up ℤ)).hom.app K))))
set_option backward.isDefEq.respectTransparency false in
private theorem identityDescent_square
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (DF : DerivedCategory A ⥤ DerivedCategory B)
    (pF : DerivedCategory.Q ⋙ DF ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (U : A ⥤ A) [U.Additive] (V : B ⥤ B) [V.Additive]
    (DU : DerivedCategory A ⥤ DerivedCategory A)
    (DV : DerivedCategory B ⥤ DerivedCategory B)
    (pU : DerivedCategory.Q ⋙ DU ≅ U.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (pV : DerivedCategory.Q ⋙ DV ≅ V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (i : U ≅ 𝟭 _) (j : V ≅ 𝟭 _) (di : DU ≅ 𝟭 _) (dj : DV ≅ 𝟭 _)
    (hi : ∀ K, di.hom.app (DerivedCategory.Q.obj K) = pU.hom.app K ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app K))
    (hj : ∀ K, dj.hom.app (DerivedCategory.Q.obj K) = pV.hom.app K ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex j (.up ℤ)).hom.app K))
    (c : U ⋙ F ≅ F ⋙ V) (dc : DU ⋙ DF ≅ DF ⋙ DV)
    (hc : ∀ M, c.hom.app M ≫ j.hom.app (F.obj M) = F.map (i.hom.app M))
    (hdc : ∀ K, dc.hom.app (DerivedCategory.Q.obj K) ≫
      DV.map (pF.hom.app K) ≫ pV.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DF.map (pU.hom.app K) ≫ pF.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app K)) :
    dc.hom ≫ whiskerLeft DF dj.hom = whiskerRight di.hom DF := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  apply (cancel_mono (pF.hom.app K)).mp
  have hn := dj.hom.naturality (pF.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, hj]
  simp only [Category.assoc]
  erw [reassoc_of% (hdc K)]
  rw [← DerivedCategory.Q.map_comp]
  have hcomplex :
      (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app K ≫
        (NatIso.mapHomologicalComplex j (.up ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app K) := by
    ext n
    exact hc (K.X n)
  rw [hcomplex, hi, DF.map_comp, Category.assoc]
  congr 1
  exact (pF.hom.naturality
    ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app K)).symm
end CategoryTheory

namespace CategoryTheory
private theorem identityUnderlying_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (V : B ⥤ C) (W : A ⥤ D) (P : D ⥤ C)
    (I : F ⋙ V ≅ W ⋙ P)
    (U : A ⥤ A) (T : B ⥤ B) (i : U ≅ 𝟭 _) (j : T ≅ 𝟭 _)
    (c : U ⋙ F ≅ F ⋙ T) (M : A)
    (u : V.obj (F.obj M) ⟶ V.obj (T.obj (F.obj M))) [IsIso u]
    (v : W.obj M ⟶ W.obj (U.obj M))
    (hu : u ≫ V.map (j.hom.app (F.obj M)) = 𝟙 _)
    (hv : v ≫ W.map (i.hom.app M) = 𝟙 _)
    (hc : u ≫ V.map (c.inv.app M) ≫ I.hom.app (U.obj M) =
      I.hom.app M ≫ P.map v) :
    V.map (c.hom.app M ≫ j.hom.app (F.obj M)) = V.map (F.map (i.hom.app M)) := by
  simp only [Functor.map_comp]
  apply (cancel_epi (V.map (c.inv.app M))).mp
  simp only [← V.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  apply (cancel_epi u).mp
  rw [hu]
  apply (cancel_mono (I.hom.app M)).mp
  rw [Category.id_comp]
  have hn := I.hom.naturality (i.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn
  simp only [Category.assoc]
  erw [hn]
  rw [reassoc_of% hc]
  simp only [← P.map_comp, hv, CategoryTheory.Functor.map_id,
    Category.comp_id]
end CategoryTheory

namespace CategoryTheory
private theorem mate_identity
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {U : C ⥤ C} {V : D ⥤ D} (i : U ≅ 𝟭 C) (j : V ≅ 𝟭 D)
    (α : U ⋙ L ⟶ L ⋙ V)
    (h : ∀ X, α.app X ≫ j.hom.app (L.obj X) = L.map (i.hom.app X))
    (Y : D) :
    (mateEquiv adj adj (.mk _ _ _ _ α)).app Y ≫ R.map (j.hom.app Y) =
      i.hom.app (R.obj Y) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := adj.counit.naturality (j.hom.app Y)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [hn]
  have ht := mateEquiv_counit adj adj (.mk _ _ _ _ α) Y
  rw [reassoc_of% ht]
  have hu := j.hom.naturality (adj.counit.app Y)
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  change V.map (adj.counit.app Y) ≫ j.hom.app Y =
    j.hom.app (L.obj (R.obj Y)) ≫ adj.counit.app Y at hu
  change α.app (R.obj Y) ≫ V.map (adj.counit.app Y) ≫ j.hom.app Y = _
  rw [hu, ← Category.assoc, h]

private theorem identity_of_mate_identity
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {U : C ⥤ C} {V : D ⥤ D} (i : U ≅ 𝟭 C) (j : V ≅ 𝟭 D)
    (α : U ⋙ L ⟶ L ⋙ V)
    (h : ∀ Y, (mateEquiv adj adj (.mk _ _ _ _ α)).app Y ≫
      R.map (j.hom.app Y) = i.hom.app (R.obj Y))
    (X : C) : α.app X ≫ j.hom.app (L.obj X) = L.map (i.hom.app X) := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  have ht := unit_mateEquiv adj adj (.mk _ _ _ _ α) X
  change U.map (adj.unit.app X) ≫
    (mateEquiv adj adj (.mk _ _ _ _ α)).app (L.obj X) =
      adj.unit.app (U.obj X) ≫ R.map (α.app X) at ht
  rw [← ht, Category.assoc, h]
  have hi := i.hom.naturality (adj.unit.app X)
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map] at hi
  rw [hi]
  exact adj.unit.naturality (i.hom.app X)
end CategoryTheory

namespace AlgebraicGeometry
private theorem strictIdentitySheaf
    {O : Type (u + 1)} [CommRing O] {ell : O}
    (a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ))
    (T : Scheme.{u}) (n : ℕ) :
    a.sheaf T n = coefficientQuotientMap (J := T.smallEtaleTopology) O ell
      (Nat.le_refl n) := by
  have h : a.ring n = Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_refl n) 1)) := by
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact a.generators n x
  unfold StrictEtaleCoefficientChange.sheaf coefficientQuotientMap
  exact congrArg (fun r ↦ (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map
    (CommRingCat.ofHom r)) h

attribute [local irreducible] coefficientQuotientSheaf CategoryTheory.sheafCompose
  SheafOfModules.siteTensorUnitUnderlying

private def normalizeEvaluation
    {C M : Type*} [Category C] [Category M]
    {E H : C ⥤ M} {A B : M ⥤ M}
    (e : E ≅ H ⋙ A) (h : A = B) (i : B ≅ 𝟭 M) : E ≅ H :=
  e ≪≫ isoWhiskerLeft H (eqToIso h) ≪≫ isoWhiskerLeft H i ≪≫ Functor.rightUnitor H

private theorem normalizeEvaluation_unit
    {C M D : Type*} [Category C] [Category M] [Category D]
    {E H : C ⥤ M} {A B : M ⥤ M}
    (e : E ≅ H ⋙ A) (h : A = B) (i : B ≅ 𝟭 M) (V : M ⥤ D) (X : C)
    (u : V.obj (H.obj X) ⟶ V.obj (E.obj X))
    (tA : V.obj (H.obj X) ⟶ V.obj (A.obj (H.obj X)))
    (tB : V.obj (H.obj X) ⟶ V.obj (B.obj (H.obj X)))
    (hu : u = tA ≫ V.map (e.inv.app X))
    (ht : tA ≫ V.map ((eqToIso h).hom.app (H.obj X)) = tB)
    (hi : tB ≫ V.map (i.hom.app (H.obj X)) = 𝟙 _) :
    u ≫ V.map ((normalizeEvaluation e h i).hom.app X) = 𝟙 _ := by
  subst u
  simp only [normalizeEvaluation, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.map_comp, Category.assoc]
  rw [← V.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [← Category.assoc]
  exact (congrArg (fun f ↦ f ≫ V.map (i.hom.app (H.obj X))) ht).trans hi

private def normalizedEvaluationData
    {C M D : Type*} [Category C] [Category M] [Category D]
    {E H : C ⥤ M} {A B : M ⥤ M}
    (e : E ≅ H ⋙ A) (h : A = B) (i : B ≅ 𝟭 M) (V : M ⥤ D)
    (u : ∀ X, V.obj (H.obj X) ⟶ V.obj (E.obj X))
    (tA : ∀ X, V.obj (H.obj X) ⟶ V.obj (A.obj (H.obj X)))
    (tB : ∀ X, V.obj (H.obj X) ⟶ V.obj (B.obj (H.obj X)))
    (hu : ∀ X, u X = tA X ≫ V.map (e.inv.app X))
    (ht : ∀ X, tA X ≫ V.map ((eqToIso h).hom.app (H.obj X)) = tB X)
    (hi : ∀ X, tB X ≫ V.map (i.hom.app (H.obj X)) = 𝟙 _) :
    { I : E ≅ H // ∀ X, u X ≫ V.map (I.hom.app X) = 𝟙 _ } :=
  ⟨normalizeEvaluation e h i, fun X ↦
    normalizeEvaluation_unit e h i V X (u X) (tA X) (tB X) (hu X) (ht X) (hi X)⟩

private theorem siteIdentityEvaluation
    {C : Type*} [Category C]
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} D]
    {R : Sheaf J CommRingCat.{w}}
    {E H : C ⥤ SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (phi psi : R ⟶ R) (h : phi = psi)
    (e : E ≅ H ⋙ siteCoefficientTensor phi)
    (i : siteCoefficientTensor psi ≅ 𝟭 _)
    (un : H ⋙ SheafOfModules.toSheaf _ ⟶ E ⋙ SheafOfModules.toSheaf _)
    (hu : ∀ X, un.app X = siteTensorUnitUnderlying phi (H.obj X) ≫
      (SheafOfModules.toSheaf _).map (e.inv.app X))
    (hi : ∀ X, siteTensorUnitUnderlying psi X ≫
      (SheafOfModules.toSheaf _).map (i.hom.app X) = 𝟙 _) :
    ∃ I : E ≅ H, ∀ X, un.app X ≫
      (SheafOfModules.toSheaf _).map (I.hom.app X) = 𝟙 _ := by
  have d := normalizedEvaluationData e (congrArg (siteCoefficientTensor (J := J)) h) i
    (SheafOfModules.toSheaf _) (fun X ↦ un.app X)
    (fun X ↦ siteTensorUnitUnderlying phi (H.obj X))
    (fun X ↦ siteTensorUnitUnderlying psi (H.obj X)) hu (fun X ↦ ?_)
    (fun X ↦ hi (H.obj X))
  · exact ⟨d.val, d.property⟩
  · subst psi
    simp

end AlgebraicGeometry
namespace AlgebraicGeometry
private theorem strictIdentityLevelPackage
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P) (n : ℕ) :
    ∃ I : U.ordinary ⋙ coefficientEvaluation (J := T.smallEtaleTopology)
        (O := O) (ell := ell) n ≅
        coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n,
      ∀ M, (U.unit n).app M ≫ (SheafOfModules.toSheaf _).map (I.hom.app M) = 𝟙 _ :=
  siteIdentityEvaluation (a.sheaf T n)
    (coefficientQuotientMap (J := T.smallEtaleTopology) O ell (Nat.le_refl n))
    (strictIdentitySheaf a T n) (U.val.evaluation n) (P.tensorUnit n)
    (U.unit n) (fun M ↦ U.property.2.1 n M) (P.tensorUnit_normalized n)

private def strictIdentityLevel
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P) (n : ℕ) :=
  (strictIdentityLevelPackage U n).choose

private theorem strictIdentityLevel_unit
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P) (n : ℕ)
    (M : strictEtaleCoefficientSystem T O ell) :
    (U.unit n).app M ≫
      (SheafOfModules.toSheaf _).map ((strictIdentityLevel U n).hom.app M) = 𝟙 _ :=
  (strictIdentityLevelPackage U n).choose_spec M

attribute [local irreducible] strictIdentityLevel

private theorem strictIdentityTransition
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P) (n : ℕ)
    (M : strictEtaleCoefficientSystem T O ell) :
    (U.unit (n + 1)).app M ≫ strictEtaleTransition (U.ordinary.obj M) n =
      strictEtaleTransition M n ≫ (U.unit n).app M := by
  have h := U.property.2.2.1 n M
  simpa only [StrictEtaleCoefficientTransport.ordinary,
    StrictEtaleCoefficientTransport.unit, OrderHom.id_coe, id_eq,
    coefficientTransitionUnderlying, P.transitionsNormalized.2.1, strictEtaleTransition,
    Nat.succ_eq_add_one, coefficientEvaluation, coefficientUnderlying,
    Functor.comp_obj, Functor.comp_map] using h


private theorem identityUnitSquare {C : Type*} [Category C]
    {A B D E : C} (u : A ⟶ B) (v : D ⟶ E)
    (i : B ≅ A) (j : E ≅ D) (f : A ⟶ D) (g : B ⟶ E)
    (hi : u ≫ i.hom = 𝟙 A) (hj : v ≫ j.hom = 𝟙 D)
    (h : u ≫ g = f ≫ v) : i.hom ≫ f = g ≫ j.hom := by
  have : IsIso u := isIso_of_comp_hom_eq_id _ hi
  apply (cancel_epi u).mp
  simp only [← Category.assoc, hi, Category.id_comp]
  rw [h, Category.assoc, hj, Category.comp_id]

private theorem strictIdentityOrdinaryTransition
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P)
    (M : strictEtaleCoefficientSystem T O ell) (n : ℕ) :
    (strictIdentityLevel U (n + 1)).hom.app M ≫ M.transition n =
      (U.ordinary.obj M).transition n ≫
        (coefficientRestriction (J := T.smallEtaleTopology) O ell (Nat.le_succ n)).map
          ((strictIdentityLevel U n).hom.app M) := by
  let e₁ := (strictIdentityLevel U (n + 1)).hom.app M
  let e₀ := (strictIdentityLevel U n).hom.app M
  let V : coefficientLevelModules (J := T.smallEtaleTopology) O ell (n + 1) ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} := SheafOfModules.toSheaf _
  apply V.map_injective
  simp only [Functor.map_comp]
  have h₁ := strictIdentityLevel_unit U (n + 1) M
  have h₀ := strictIdentityLevel_unit U n M
  have ht := strictIdentityTransition U n M
  dsimp only [OrderHom.id_coe, id_eq, coefficientEvaluation, Functor.comp_obj] at h₁ h₀
  have hc := identityUnitSquare ((U.unit (n + 1)).app M) ((U.unit n).app M)
    (V.mapIso ((strictIdentityLevel U (n + 1)).app M))
    ((SheafOfModules.toSheaf _).mapIso ((strictIdentityLevel U n).app M))
    (strictEtaleTransition M n) (strictEtaleTransition (U.ordinary.obj M) n) h₁ h₀ ht
  have hn := (siteScalarUnderlyingIso
    (coefficientQuotientMap (J := T.smallEtaleTopology) O ell (Nat.le_succ n))).hom.naturality e₀
  dsimp only [Functor.comp_map] at hn
  apply (cancel_mono ((siteScalarUnderlyingIso
    (coefficientQuotientMap (J := T.smallEtaleTopology) O ell (Nat.le_succ n))).hom.app
      (M.level n))).mp
  dsimp only [V, e₀, coefficientEvaluation, Functor.comp_obj] at hn ⊢
  simp only [Nat.succ_eq_add_one] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [V, e₀, Functor.mapIso_hom, Iso.app_hom, strictEtaleTransition,
    Category.assoc, OrderHom.id_coe, id_eq, Functor.comp_obj, coefficientEvaluation,
    Nat.succ_eq_add_one] using hc



private def strictIdentityOrdinary
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P) : U.ordinary ≅ 𝟭 _ :=
  SheafOfModules.systemNatIso U.ordinary (strictIdentityLevel U)
    (strictIdentityOrdinaryTransition U)

private theorem strictIdentityOrdinary_app
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P)
    (M : strictEtaleCoefficientSystem T O ell) (n : ℕ) :
    ((strictIdentityOrdinary U).hom.app M).app n =
      (strictIdentityLevel U n).hom.app M := rfl

attribute [local irreducible] strictIdentityOrdinary

private def strictIdentityDerived
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P) : U.derived ≅ 𝟭 _ :=
  (CategoryTheory.identityDescent U.ordinary U.derived U.factors
    (strictIdentityOrdinary U)).val

private theorem strictIdentityDerived_rep
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P)
    (K : CochainComplex (strictEtaleCoefficientSystem T O ell) ℤ) :
    (strictIdentityDerived U).hom.app (DerivedCategory.Q.obj K) =
      U.factors.hom.app K ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (strictIdentityOrdinary U) (.up ℤ)).hom.app K) :=
  (CategoryTheory.identityDescent U.ordinary U.derived U.factors
    (strictIdentityOrdinary U)).property K

attribute [local irreducible] strictIdentityDerived

private def strictIdentity
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}} {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P) : StrictEtaleTransportIdentity U := by
  refine ⟨⟨strictIdentityOrdinary U, strictIdentityDerived U⟩, ?_,
    strictIdentityDerived_rep U⟩
  intro n M
  change (U.unit n).app M ≫ (SheafOfModules.toSheaf _).map
    (((strictIdentityOrdinary U).hom.app M).app n) = 𝟙 _
  rw [strictIdentityOrdinary_app]
  exact strictIdentityLevel_unit U n M
end AlgebraicGeometry
namespace AlgebraicGeometry
attribute [local irreducible] strictIdentityLevel strictIdentityOrdinary strictIdentityDerived

private theorem mappedIdentityUnit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (E : A ⥤ B) (F : B ⥤ C) (G : C ⥤ D) (U : A ⥤ A) (i : U ≅ 𝟭 _)
    (un : E ⋙ F ⟶ U ⋙ E ⋙ F) (X : A)
    (h : un.app X ≫ F.map (E.map (i.hom.app X)) = 𝟙 _) :
    (whiskerRight un G).app X ≫ (E ⋙ F ⋙ G).map (i.hom.app X) = 𝟙 _ := by
  exact (G.map_comp _ _).symm.trans ((congrArg G.map h).trans (G.map_id _))

private theorem strictIdentityInverseOrdinary
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PT : StrictEtaleEvaluation T O ell} {PS : StrictEtaleEvaluation S O ell}
    (UT : StrictEtaleCoefficientTransport a T PT PT)
    (US : StrictEtaleCoefficientTransport a S PS PS)
    (A : StrictEtaleOrdinaryImage O ell g)
    (DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj)
    (C : StrictEtaleInverseTransport UT US A A DA DA)
    (M : strictEtaleCoefficientSystem S O ell) :
    C.val.1.hom.app M ≫ (strictIdentityOrdinary UT).hom.app (A.inverse.obj M) =
      A.inverse.map ((strictIdentityOrdinary US).hom.app M) := by
  apply SheafOfModules.systemHom_ext
  intro n
  apply (coefficientUnderlying (J := T.smallEtaleTopology) O ell n).map_injective
  let V := coefficientUnderlying (J := T.smallEtaleTopology) O ell n
  let ev := coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n
  have hut : (UT.setUnit n).app (A.inverse.obj M) ≫
      V.map (ev.map ((strictIdentityOrdinary UT).hom.app (A.inverse.obj M))) = 𝟙 _ :=
    mappedIdentityUnit ev (SheafOfModules.toSheaf _) (sheafCompose T.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})) UT.ordinary (strictIdentityOrdinary UT)
      (UT.unit n) (A.inverse.obj M) (by
        change (UT.unit n).app (A.inverse.obj M) ≫ (SheafOfModules.toSheaf _).map
          (((strictIdentityOrdinary UT).hom.app (A.inverse.obj M)).app n) = 𝟙 _
        rw [strictIdentityOrdinary_app]
        exact strictIdentityLevel_unit UT n (A.inverse.obj M))
  have hus : (US.setUnit n).app M ≫
      (coefficientUnderlying (J := S.smallEtaleTopology) O ell n).map
        ((coefficientEvaluation (J := S.smallEtaleTopology) (O := O) (ell := ell) n).map
          ((strictIdentityOrdinary US).hom.app M)) = 𝟙 _ :=
    mappedIdentityUnit (coefficientEvaluation (J := S.smallEtaleTopology)
      (O := O) (ell := ell) n) (SheafOfModules.toSheaf _)
      (sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))
      US.ordinary (strictIdentityOrdinary US) (US.unit n) M (by
        change (US.unit n).app M ≫ (SheafOfModules.toSheaf _).map
          (((strictIdentityOrdinary US).hom.app M).app n) = 𝟙 _
        rw [strictIdentityOrdinary_app]
        exact strictIdentityLevel_unit US n M)
  have hmap : IsIso (V.map (ev.map ((strictIdentityOrdinary UT).hom.app
      (A.inverse.obj M)))) := by
    change IsIso ((V.mapIso (ev.mapIso ((strictIdentityOrdinary UT).app
      (A.inverse.obj M)))).hom)
    infer_instance
  have hunit : IsIso ((UT.setUnit n).app (A.inverse.obj M)) :=
    @isIso_of_comp_hom_eq_id _ _ _ _ _ hmap _ hut
  exact @CategoryTheory.identityUnderlying_square _ _ _ _ _ _ _ _ A.inverse
    ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) ⋙ V)
    ((coefficientEvaluation (J := S.smallEtaleTopology) (O := O) (ell := ell) n) ⋙
      coefficientUnderlying (J := S.smallEtaleTopology) O ell n)
    (Scheme.etaleSetPullback g) (strictEtaleInverseUnderlying A n)
    US.ordinary UT.ordinary (strictIdentityOrdinary US) (strictIdentityOrdinary UT)
    C.val.1 M ((UT.setUnit n).app (A.inverse.obj M)) hunit ((US.setUnit n).app M)
    hut hus (C.property.1 n M)

private theorem strictIdentityInverseDerived
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PT : StrictEtaleEvaluation T O ell} {PS : StrictEtaleEvaluation S O ell}
    (UT : StrictEtaleCoefficientTransport a T PT PT)
    (US : StrictEtaleCoefficientTransport a S PS PS)
    (A : StrictEtaleOrdinaryImage O ell g)
    (DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj)
    (C : StrictEtaleInverseTransport UT US A A DA DA) :
    C.derived.hom ≫ whiskerLeft DA.inverse (strictIdentityDerived UT).hom =
      whiskerRight (strictIdentityDerived US).hom DA.inverse :=
  CategoryTheory.identityDescent_square A.inverse DA.inverse DA.inverseFactors
    US.ordinary UT.ordinary US.derived UT.derived US.factors UT.factors
    (strictIdentityOrdinary US) (strictIdentityOrdinary UT)
    (strictIdentityDerived US) (strictIdentityDerived UT)
    (strictIdentityDerived_rep US) (strictIdentityDerived_rep UT) C.val.1 C.derived
    (strictIdentityInverseOrdinary UT US A DA C) C.property.2
end AlgebraicGeometry

namespace AlgebraicGeometry
private theorem strictIdentityOpen
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c}
    {TX : StrictEtaleCoefficientTransport a X S.PX S.PX}
    {TY : StrictEtaleCoefficientTransport a Y S.PY S.PY}
    {TZ : StrictEtaleCoefficientTransport a c.Z S.PZ S.PZ}
    (P : StrictEtaleCompactSupportTransport a c S S TX TY TZ) (K) :
    P.openComparison.hom.app K ≫ (strictIdentityDerived TZ).hom.app
        (S.derivedOpen.obj K) = S.derivedOpen.map ((strictIdentityDerived TX).hom.app K) := by
  apply CategoryTheory.identity_of_mate_identity S.derivedOpenAdjunction
    (strictIdentityDerived TX) (strictIdentityDerived TZ) P.openComparison.hom
  intro M
  rw [show (mateEquiv S.derivedOpenAdjunction S.derivedOpenAdjunction
      (.mk _ _ _ _ P.openComparison.hom)).app M =
        P.val.openSquare.derived.inv.app M from congr_app P.property.1 M]
  have h := congr_app (strictIdentityInverseDerived TX TZ S.openImage
    S.openDerived.system P.val.openSquare) M
  dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at h
  apply (cancel_epi (P.val.openSquare.derived.hom.app M)).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact h.symm

private theorem strictIdentityProper
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c}
    {TX : StrictEtaleCoefficientTransport a X S.PX S.PX}
    {TY : StrictEtaleCoefficientTransport a Y S.PY S.PY}
    {TZ : StrictEtaleCoefficientTransport a c.Z S.PZ S.PZ}
    (P : StrictEtaleCompactSupportTransport a c S S TX TY TZ) (K) :
    P.properComparison.hom.app K ≫ S.properDerived.system.direct.map
        ((strictIdentityDerived TZ).hom.app K) =
      (strictIdentityDerived TY).hom.app (S.properDerived.system.direct.obj K) := by
  rw [show P.properComparison.hom =
    (mateEquiv S.properDerived.system.adjunction S.properDerived.system.adjunction
      (.mk _ _ _ _ P.val.properSquare.derived.hom)).natTrans from P.property.2]
  apply CategoryTheory.mate_identity S.properDerived.system.adjunction
    (strictIdentityDerived TY) (strictIdentityDerived TZ)
  intro M
  exact congr_app (strictIdentityInverseDerived TZ TY S.properImage
    S.properDerived.system P.val.properSquare) M

private theorem strictIdentityProjection
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c}
    {TX : StrictEtaleCoefficientTransport a X S.PX S.PX}
    {TY : StrictEtaleCoefficientTransport a Y S.PY S.PY}
    {TZ : StrictEtaleCoefficientTransport a c.Z S.PZ S.PZ}
    (P : StrictEtaleCompactSupportTransport a c S S TX TY TZ) (K) :
    P.projection.inv.app K ≫ (strictIdentityDerived TY).hom.app (S.functor.obj K) =
      S.functor.map ((strictIdentityDerived TX).hom.app K) := by
  simp only [StrictEtaleCompactSupportTransport.projection, Iso.trans_inv,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    isoWhiskerLeft_inv, whiskerLeft_app, isoWhiskerRight_inv, whiskerRight_app,
    Iso.symm_inv, Category.comp_id]
  have hp := strictIdentityProper P (S.derivedOpen.obj K)
  have ho := strictIdentityOpen P K
  have hp' : P.properComparison.inv.app (S.derivedOpen.obj K) ≫
      (strictIdentityDerived TY).hom.app (S.functor.obj K) =
        S.properDerived.system.direct.map
          ((strictIdentityDerived TZ).hom.app (S.derivedOpen.obj K)) := by
    apply (cancel_epi (P.properComparison.hom.app (S.derivedOpen.obj K))).mp
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    exact hp.symm
  dsimp only [StrictEtaleCompactSupport.functor, Functor.comp_obj] at hp' ⊢
  simp only [Category.assoc, Category.id_comp, Category.comp_id]
  change S.properDerived.system.direct.map (P.openComparison.hom.app K) ≫
      P.properComparison.inv.app (S.derivedOpen.obj K) ≫
        (strictIdentityDerived TY).hom.app
          (S.properDerived.system.direct.obj (S.derivedOpen.obj K)) = _
  erw [hp', ← S.properDerived.system.direct.map_comp, ho]
  rfl
end AlgebraicGeometry

namespace AlgebraicGeometry

/-- Identity coefficient extension has the identity exceptional comparison, with the
canonical tensor units. Source: Zheng, Proposition 2.29(2) and Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: tensor unit maps determine the ordinary identity identifications. Localize
these maps on complexes. Under the displayed unit identifications, the transpose
of the exceptional comparison is the adjunction counit. The triangle identity and
injectivity of the adjunction Hom bijection therefore give the displayed equality. -/
theorem strictEtaleExceptionalTransport_identity
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c}
    {G : StrictEtaleExceptionalAdjoint O ell c S}
    {TX : StrictEtaleCoefficientTransport a X S.PX S.PX}
    {TY : StrictEtaleCoefficientTransport a Y S.PY S.PY}
    {TZ : StrictEtaleCoefficientTransport a c.Z S.PZ S.PZ}
    (C : StrictEtaleExceptionalTransport a c S S TX TY TZ G G) :
    ∃ (IX : StrictEtaleTransportIdentity TX) (IY : StrictEtaleTransportIdentity TY)
      (_IZ : StrictEtaleTransportIdentity TZ),
      ∀ M, C.right.hom.app M ≫ G.right.map (IY.derived.hom.app M) =
        IX.derived.hom.app (G.right.obj M) := by
  refine ⟨strictIdentity TX, strictIdentity TY, strictIdentity TZ, ?_⟩
  intro M
  rw [show C.right.hom =
    (mateEquiv G.adjunction G.adjunction
      (.mk _ _ _ _ C.val.compact.projection.inv)).natTrans from C.property.1]
  exact CategoryTheory.mate_identity G.adjunction
    (strictIdentityDerived TX) (strictIdentityDerived TY)
    C.val.compact.projection.inv (strictIdentityProjection C.val.compact) M

end AlgebraicGeometry
end IdentityTransportProof

namespace CategoryTheory
private theorem coefficientMate_composition
    {A₁ B₁ A₂ B₂ A₃ B₃ : Type*}
    [Category A₁] [Category B₁] [Category A₂] [Category B₂]
    [Category A₃] [Category B₃]
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
    {L₃ : A₃ ⥤ B₃} {R₃ : B₃ ⥤ A₃}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {U₁₂ : A₁ ⥤ A₂} {U₂₃ : A₂ ⥤ A₃} {U₁₃ : A₁ ⥤ A₃}
    {V₁₂ : B₁ ⥤ B₂} {V₂₃ : B₂ ⥤ B₃} {V₁₃ : B₁ ⥤ B₃}
    (i : U₁₂ ⋙ U₂₃ ≅ U₁₃) (j : V₁₂ ⋙ V₂₃ ≅ V₁₃)
    (p₁₂ : U₁₂ ⋙ L₂ ⟶ L₁ ⋙ V₁₂) (p₂₃ : U₂₃ ⋙ L₃ ⟶ L₂ ⋙ V₂₃)
    (p₁₃ : U₁₃ ⋙ L₃ ⟶ L₁ ⋙ V₁₃)
    (h : ∀ K, L₃.map (i.hom.app K) ≫ p₁₃.app K =
      p₂₃.app (U₁₂.obj K) ≫ V₂₃.map (p₁₂.app K) ≫ j.hom.app (L₁.obj K))
    (M : B₁) :
    i.hom.app (R₁.obj M) ≫ (mateEquiv a₁ a₃ (.mk _ _ _ _ p₁₃)).natTrans.app M =
      U₂₃.map ((mateEquiv a₁ a₂ (.mk _ _ _ _ p₁₂)).natTrans.app M) ≫
        (mateEquiv a₂ a₃ (.mk _ _ _ _ p₂₃)).natTrans.app (V₁₂.obj M) ≫
          R₃.map (j.hom.app M) := by
  apply (a₃.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit a₁ a₃ (.mk _ _ _ _ p₁₃) M]
  rw [← Category.assoc, h]
  have hn := a₃.counit.naturality (j.hom.app M)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [hn]
  rw [reassoc_of% (mateEquiv_counit a₂ a₃ (.mk _ _ _ _ p₂₃) (V₁₂.obj M))]
  have hp0 := p₂₃.naturality ((mateEquiv a₁ a₂ (.mk _ _ _ _ p₁₂)).natTrans.app M)
  have hp : L₃.map (U₂₃.map ((mateEquiv a₁ a₂ (.mk _ _ _ _ p₁₂)).natTrans.app M)) ≫
      p₂₃.app (R₂.obj (V₁₂.obj M)) =
      p₂₃.app (U₁₂.obj (R₁.obj M)) ≫
        V₂₃.map (L₂.map ((mateEquiv a₁ a₂ (.mk _ _ _ _ p₁₂)).natTrans.app M)) := by
    simpa only [Functor.comp_map, Functor.comp_obj] using hp0
  dsimp only [TwoSquare.mk]
  rw [reassoc_of% hp]
  simp only [Category.assoc]
  rw [← V₂₃.map_comp_assoc, mateEquiv_counit a₁ a₂ (.mk _ _ _ _ p₁₂) M,
    V₂₃.map_comp]
  have hj := j.hom.naturality (a₁.counit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hj
  dsimp only [TwoSquare.mk]
  simp only [Category.assoc]
  rw [hj]
end CategoryTheory

namespace AlgebraicGeometry
/-- Composition of coefficient changes and reindexings respects the canonical tensor
associators as an equality of actual system maps. Source: Zheng, Construction 5.15
and Proposition 2.29(2) (blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: the ordinary tensor associator is fixed by sending the composite tensor unit
to the single tensor unit. Descent gives the representative-normalized derived
associators. Transpose the composite of the two exceptional comparisons. Substitute
the defining counit-mate equations twice and use counit naturality. The two inverse
projection squares compose to the single inverse projection square, since their
inverse-image normalizations agree on tensor units. Injectivity of the Hom bijection
identifies the transposes and proves the equality. This applies to composed cofinal
restrictions too; no faithfulness of evaluation on derived morphisms is used. -/
theorem strictEtaleExceptionalTransport_comp
    {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂}
    {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S₁ : StrictEtaleCompactSupport O₁ ell₁ c}
    {S₂ : StrictEtaleCompactSupport O₂ ell₂ c}
    {S₃ : StrictEtaleCompactSupport O₃ ell₃ c}
    {G₁ : StrictEtaleExceptionalAdjoint O₁ ell₁ c S₁}
    {G₂ : StrictEtaleExceptionalAdjoint O₂ ell₂ c S₂}
    {G₃ : StrictEtaleExceptionalAdjoint O₃ ell₃ c S₃}
    {X₁₂ : StrictEtaleCoefficientTransport a X S₁.PX S₂.PX}
    {Y₁₂ : StrictEtaleCoefficientTransport a Y S₁.PY S₂.PY}
    {Z₁₂ : StrictEtaleCoefficientTransport a c.Z S₁.PZ S₂.PZ}
    {X₂₃ : StrictEtaleCoefficientTransport b X S₂.PX S₃.PX}
    {Y₂₃ : StrictEtaleCoefficientTransport b Y S₂.PY S₃.PY}
    {Z₂₃ : StrictEtaleCoefficientTransport b c.Z S₂.PZ S₃.PZ}
    {X₁₃ : StrictEtaleCoefficientTransport (a.comp b) X S₁.PX S₃.PX}
    {Y₁₃ : StrictEtaleCoefficientTransport (a.comp b) Y S₁.PY S₃.PY}
    {Z₁₃ : StrictEtaleCoefficientTransport (a.comp b) c.Z S₁.PZ S₃.PZ}
    (C₁₂ : StrictEtaleExceptionalTransport a c S₁ S₂ X₁₂ Y₁₂ Z₁₂ G₁ G₂)
    (C₂₃ : StrictEtaleExceptionalTransport b c S₂ S₃ X₂₃ Y₂₃ Z₂₃ G₂ G₃)
    (C₁₃ : StrictEtaleExceptionalTransport (a.comp b) c S₁ S₃ X₁₃ Y₁₃ Z₁₃ G₁ G₃) :
    ∃ (AX : StrictEtaleTransportComposition X₁₂ X₂₃ X₁₃)
      (AY : StrictEtaleTransportComposition Y₁₂ Y₂₃ Y₁₃)
      (_AZ : StrictEtaleTransportComposition Z₁₂ Z₂₃ Z₁₃),
      ∀ M, AX.derived.hom.app (G₁.right.obj M) ≫ C₁₃.right.hom.app M =
        X₂₃.derived.map (C₁₂.right.hom.app M) ≫
          C₂₃.right.hom.app (Y₁₂.derived.obj M) ≫ G₃.right.map (AY.derived.hom.app M) := by
  obtain ⟨AX, AY, AZ, hprojection⟩ := strictEtaleCompactSupportTransport_composition
    C₁₂.val.compact C₂₃.val.compact C₁₃.val.compact
  refine ⟨AX, AY, AZ, ?_⟩
  intro M
  rw [show C₁₃.right.hom = (mateEquiv G₁.adjunction G₃.adjunction
    (.mk _ _ _ _ C₁₃.val.compact.projection.inv)).natTrans from C₁₃.property.1]
  rw [show C₁₂.right.hom = (mateEquiv G₁.adjunction G₂.adjunction
    (.mk _ _ _ _ C₁₂.val.compact.projection.inv)).natTrans from C₁₂.property.1]
  rw [show C₂₃.right.hom = (mateEquiv G₂.adjunction G₃.adjunction
    (.mk _ _ _ _ C₂₃.val.compact.projection.inv)).natTrans from C₂₃.property.1]
  exact CategoryTheory.coefficientMate_composition G₁.adjunction G₂.adjunction G₃.adjunction
    AX.derived AY.derived C₁₂.val.compact.projection.inv C₂₃.val.compact.projection.inv
    C₁₃.val.compact.projection.inv hprojection M
end AlgebraicGeometry
