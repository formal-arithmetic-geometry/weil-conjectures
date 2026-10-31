/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientReductionCore
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.QuotientOrdinaryModels
import WeilConjectures.AlgebraicGeometry.QuotientConstantKFlat
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.SystemEvaluationKFlat
import all WeilConjectures.Algebra.Homology.TotalTensorHomotopyConeSigns
import all WeilConjectures.Algebra.Homology.ScalarHomExtensionKFlat

/-! # Flat-term K-flat quotient systems

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7E, 06YY, 07A2 and 06YP;
whole-system refinement extracted from the primitive counit comparison
(blueprint: lem-pur-quotient-system-flat-models).

All systems are actual module sheaves on the vertical sequence site. Scalar extension
is the recorded sheafified extension, and tensor is the recorded direct-sum total tensor.

## Main definitions and statements

- `quotientReduction`: the strict reduction functor over the actual sequence ring.
- `QuotientSystemFlatModels`, `quotientSystemFlatModels`: its simultaneous model properties.
- `quotientTensorComparison`: the canonical whole-derived-system tensor isomorphism.
- `quotientInverseImageComparison`: the canonical whole-system inverse-image isomorphism.
- `quotientTensor_transition`, `quotientSystemInverseImage`: transitions and preservation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v r a b
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] hasDerived SheafOfModules.monoidalCategory evaluation
attribute [local instance 10000] hasDerived SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive

-- Expose only the thin ordinary wrappers to implicit argument checking.
attribute [local implicit_reducible] SheafOfModules.restrictScalars
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj' quotientConstant sheafCompose
  PresheafOfModules.presheaf PresheafOfModules.sheafification
  PresheafOfModules.sheafify PresheafOfModules.ofPresheaf
  SheafOfModules.changeOfRingsPresheaf SheafOfModules.changeOfRings
  Functor.ofSequence Functor.ofOpSequence
  Functor.mapHomologicalComplex Functor.map₂HomologicalComplex coefficientTotalTensor
  systemRing ringPresheaf rings
  SheafOfModules.systemSequenceRing SheafOfModules.systemSequenceRingPresheaf
  SheafOfModules.systemSequenceEvaluation
  SheafOfModules.strictSystemSequenceEquivalence

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)

variable [small : EssentiallySmall.{max c v r} C]
variable (R : Sheaf J CommRingCat.{max c v r})
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (α : ∀ n : ℕ, R ⟶ B n)
  (hα : ∀ n : ℕ, α (n + 1) ≫ τ n = α n)

/-- Flat-term K-flat models, their whole-system derived scalar comparison, and their
whole-system tensor comparison. All scalar functors carry the existing canonical
ordinary and derived normalization, rather than arbitrary choices of maps.
Source: Stacks 0G7E, 06YY, 07A2, 06YP
(blueprint: lem-pur-quotient-system-flat-models). -/
structure QuotientSystemFlatModels (A : Data.{c, v, r} J B τ) where
  /-- Derived scalar extension along the actual map from the constant ring system. -/
  scalar : ScalarData.{c, v, max c v r} (quotientRingMap.{c, v, r} J R B τ α hα)
  /-- The same ordinary sheafified extension at each level. -/
  levels : ∀ n : ℕ, ScalarData.{c, v, max c v r} (α n)
  /-- The defining level formula D_B(M)_n = M tensor_R B_n, natural for all maps. -/
  reductionEvaluation : ∀ n : ℕ,
    quotientConstant.{c, v, r} J R ⋙ scalar.model.E ⋙ evaluation.{c, v, max c v r} J B τ n ≅
      (levels n).model.E
  /-- Evaluation is the canonical extension comparison on the generators 1 tensor x. -/
  evaluation_unit : ∀ (M : Mod.{c, v, max c v r} J R) (n : ℕ) (U : Cᵒᵖ)
    (x : M.val.obj U)
    (y : ((evaluation.{c, v, max c v r} J B τ n).obj
      (scalar.model.E.obj ((quotientConstant.{c, v, r} J R).obj M))).val.obj U),
    HEq y (scalarExtensionSection.{c, v, r} (quotientRingMap.{c, v, r} J R B τ α hα)
      scalar ((quotientConstant.{c, v, r} J R).obj M) (op (n, U.unop)) x) →
    HEq (((reductionEvaluation n).hom.app M).val.app U y)
      (scalarExtensionSection.{c, v, r} (α n) (levels n) M U x)
  /-- The strict horizontal map is 1 tensor the coefficient transition. -/
  reduction_transition : ∀ (M : Mod.{c, v, max c v r} J R) (n : ℕ) (U : Cᵒᵖ)
    (x : M.val.obj U)
    (y : ((evaluation.{c, v, max c v r} J B τ (n + 1)).obj
      (scalar.model.E.obj ((quotientConstant.{c, v, r} J R).obj M))).val.obj U),
    HEq y (scalarExtensionSection.{c, v, r} (quotientRingMap.{c, v, r} J R B τ α hα)
      scalar ((quotientConstant.{c, v, r} J R).obj M) (op (n + 1, U.unop)) x) →
    HEq (((transition.{c, v, max c v r} J B τ (Nat.le_succ n)).app
      ((quotientConstant.{c, v, r} J R ⋙ scalar.model.E).obj M)).val.app U y)
      (scalarExtensionSection.{c, v, r} (quotientRingMap.{c, v, r} J R B τ α hα)
        scalar ((quotientConstant.{c, v, r} J R).obj M) (op (n, U.unop)) x)
  /-- The whole reduction has flat terms and is K-flat on the sequence site. -/
  good : ∀ P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ,
    P.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R P →
      ((quotientReduction.{c, v, r} J R B τ α hα scalar).obj P).IsKFlatIndependentCoefficients ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
        ((quotientReduction.{c, v, r} J R B τ α hα scalar).obj P)
  /-- Every level has flat terms and is K-flat, without flat coefficient maps. -/
  level_good : ∀ (P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ),
    P.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R P → ∀ n : ℕ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj
          ((quotientReduction.{c, v, r} J R B τ α hα scalar).obj P)) ∧
      flatTerms.{c, v, r} J (B n) (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex
      (.up ℤ)).obj
        ((quotientReduction.{c, v, r} J R B τ α hα scalar).obj P))
  /-- Reduction preserves quasi-isomorphisms of all good inputs, componentwise. -/
  quasiIso : ∀ {P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ} (f : P ⟶ Q),
    P.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R P →
    Q.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R Q → QuasiIso f → ∀ n : ℕ,
      QuasiIso (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).map
        ((quotientReduction.{c, v, r} J R B τ α hα scalar).map f))
  /-- The canonical derived scalar counit computes the whole reduction. -/
  computes : ∀ P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ,
    P.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R P →
      IsIso (scalar.model.ε.app
        (((quotientConstant.{c, v, r} J R).mapHomologicalComplex (.up ℤ)).obj P))
  /-- Tensor preserves quasi-isomorphisms in either good input, at every level. -/
  tensor_quasiIso : ∀ {P P' Q Q' : CochainComplex (Mod.{c, v, max c v r} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q'),
    P.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R P →
    P'.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R P' →
    Q.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R Q →
    Q'.IsKFlatIndependentCoefficients → flatTerms.{c, v, r} J R Q' →
    QuasiIso f → QuasiIso g → ∀ n : ℕ,
      QuasiIso (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).map
        ((quotientTensor.{c, v, r} J R B τ α hα scalar).map (Prod.mkHom f g)))

  /-- The total tensor has the displayed level complex, through the normalized summand map. -/
  tensor_level : ∀ (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ) (n : ℕ),
    IsIso ((A.tensorEvaluationModel n).chain
      ((quotientReduction.{c, v, r} J R B τ α hα scalar).obj P)
      ((quotientReduction.{c, v, r} J R B τ α hα scalar).obj Q))

/-- The canonical whole-system tensor comparison, obtained from the recorded natural
K-flat representative comparison on the actual total tensor. It is natural for all
cochain maps of good inputs by CoefficientTensorModels.comparison.naturality.
Source: Stacks 06YN, 07A4 (blueprint: lem-pur-quotient-system-flat-models). -/
def quotientTensorComparison (A : Data.{c, v, r} J B τ)
    (M : QuotientSystemFlatModels.{c, v, r} J R B τ α hα A)
    (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (fP : flatTerms.{c, v, r} J R P)
    (hQ : Q.IsKFlatIndependentCoefficients) (fQ : flatTerms.{c, v, r} J R Q) :=
  tensorModelIso.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) A.closed A.tensorModels
    ((quotientReduction.{c, v, r} J R B τ α hα M.scalar).obj P)
    ((quotientReduction.{c, v, r} J R B τ α hα M.scalar).obj Q)
    (M.good P hP fP).1 (M.good Q hQ fQ).1

/-- Horizontal restriction of a tensor summand is the tensor of the horizontal
restrictions. This is the transition formula of Z_T before localization; total tensor
uses these maps on each (p,q) summand, with no change of the differential sign.
Source: Stacks 03EK, 06YN (blueprint: lem-pur-quotient-system-flat-models).
Proof: the presheaf tensor restriction is the tensor of the two restrictions.
Naturality of the sheafification unit carries the same formula to the sheaf tensor.
The total summand inclusions commute with horizontal restrictions by their naturality.
The strict squares for maps follow from naturality of those maps as module sheaf maps. -/
theorem quotientTensor_transition
    (M N : Systems.{c, v, max c v r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (x : M.val.obj (op (n + 1, U.unop))) (y : N.val.obj (op (n + 1, U.unop))) :
    (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) M N).val.map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op
        (tensorSection.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N (op (n + 1, U.unop)) x y) =
      tensorSection.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) M N (op (n, U.unop))
          (M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x)
          (N.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op y) := by
  let R' := systemRing.{c, v, max c v r} J B τ
  let J' := coefficientSequenceTopology J
  let := abelianSheafify.{c, v, max c v r} J'
  let := locallyBijective.{c, v, max c v r} J'
  let := SheafOfModules.isMonoidal_W_independentCoefficients R'
  let := SheafOfModules.monoidalCategory R'
  let t : M.val ⊗ N.val ⟶ (ordinaryTensor.{c, v, r} J' R' M N).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ring J' R').obj)).unit.app
        (M.val ⊗ N.val) ≫
      (SheafOfModules.tensorObjIsoSheafification (R := R') M N).inv.val
  exact (PresheafOfModules.naturality_apply t
    (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op
      (x ⊗ₜ[R'.obj.obj (op (n + 1, U.unop))] y)).symm

/-- The strict inverse-image system Z_F, computed termwise on the whole reduction.
Source: Stacks 0G7E, 06YY; Zheng 4.1
(blueprint: lem-pur-quotient-system-flat-models). -/
def quotientInverseImage (A : Data.{c, v, r} J B τ)
    (S : ScalarData.{c, v, max c v r} (quotientRingMap.{c, v, r} J R B τ α hα))
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) (G : Geometry.{c, v, r} J B τ A J' uInv uPush adj) :=
  quotientReduction.{c, v, r} J R B τ α hα S ⋙ G.pull.mapHomologicalComplex (.up ℤ)

/-- The representative comparison for inverse image is the canonical localization
comparison, hence natural for every cochain map before evaluation.
Source: Stacks 06YY (blueprint: lem-pur-quotient-system-flat-models). -/
def quotientInverseImageComparison (A : Data.{c, v, r} J B τ)
    (S : ScalarData.{c, v, max c v r} (quotientRingMap.{c, v, r} J R B τ α hα))
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) (G : Geometry.{c, v, r} J B τ A J' uInv uPush adj) :
    quotientReduction.{c, v, r} J R B τ α hα S ⋙ DerivedCategory.Q ⋙
        G.pull.mapDerivedCategory ≅
      quotientInverseImage.{c, v, r} J R B τ α hα A S J' uInv uPush adj G ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft (quotientReduction.{c, v, r} J R B τ α hα S)
    (Functor.mapDerivedCategoryFactors G.pull)

attribute [local irreducible] quotientConstantRing quotientRingMap

section
attribute [local semireducible] hasDerived
attribute [local implicit_reducible] hasDerived SheafOfModules.systemRingHasDerived

private theorem quotientScalar_exists {S T : Sheaf J CommRingCat.{max c v r}}
    (φ : S ⟶ T) : Nonempty (ScalarData.{c, v, max c v r} φ) := by
  classical
  obtain ⟨A⟩ := SheafOfModules.nonempty_systemScalarModel.{c, v, max c v r} φ
  refine ⟨{
    model := A.model
    ordinaryAdjunction := A.ordinaryAdj
    unit_section := ?_
    adjunction := A.adjunction
    transpose_model := ?_ }⟩
  · intro M U x
    rw [A.unit_normalized]
    dsimp only [SheafOfModules.systemModelTmul]
    rw [one_smul]
    change (eqToHom (C := Mod J T) _).val.app U
      ((eqToHom (C := Mod J T) _).val.app U _) = _
    rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val, eqToHom_trans]
    rfl
  · intro P Q hP f
    rw [A.transpose]
    simp

end

private theorem quotientScalar_section {S T : Sheaf J CommRingCat.{max c v r}}
    (φ : S ⟶ T) (A : ScalarData.{c, v, max c v r} φ)
    (M : Mod.{c, v, max c v r} J S) (U : Cᵒᵖ) (x : M.val.obj U) :
    scalarExtensionSection.{c, v, r} φ A M U x =
      (A.ordinaryAdjunction.unit.app M).val.app U x := by
  unfold scalarExtensionSection
  rw [← A.unit_section M U x]
  rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans]
  rfl

private theorem quotientScalar_good
    {S T : Sheaf J CommRingCat.{max c v r}} (φ : S ⟶ T)
    (A : ScalarData.{c, v, max c v r} φ)
    (P : CochainComplex (Mod.{c, v, max c v r} J S) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (fP : flatTerms.{c, v, r} J S P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := T)
      ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ∧
      flatTerms.{c, v, r} J T ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) := by
  refine ⟨?_, ?_⟩
  · exact SheafOfModules.kflatOfScalarExtensionIdentification φ A.model.E
      A.model.obj_eq A.model.map_eq P hP
  · intro i
    change SheafOfModules.IsFlatOnSite (A.model.E.obj (P.X i))
    rw [A.model.obj_eq]
    exact SheafOfModules.isFlat_changeOfRingsOfUniverses φ (P.X i) (fP i)

private theorem quotientEvaluation_eq (n : ℕ) :
    evaluation.{c, v, max c v r} J B τ n =
      SheafOfModules.systemSequenceEvaluation (rings.{c, v, max c v r} J B τ) n := by
  unfold evaluation
  have he : eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm =
      SheafOfModules.systemSequenceVerticalRingMap (rings.{c, v, max c v r} J B τ) n := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    simp only [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  exact congrArg (fun φ ↦ SheafOfModules.pushforward (F := Prod.sectR n C) φ) he

private theorem quotientEvaluation_good
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P) (n : ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients (R := B n)
      (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P) ∧
    flatTerms.{c, v, r} J (B n)
      (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := SheafOfModules.systemSequenceEvaluation_preservesKFlat
    (rings.{c, v, max c v r} J B τ) n P hP fP
  have : (evaluation.{c, v, max c v r} J B τ n).Additive :=
    evaluationAdditive.{c, v, max c v r} J B τ n
  let ei := eqToIso (quotientEvaluation_eq.{c, v, r} J B τ n)
  have : (SheafOfModules.systemSequenceEvaluation
      (rings.{c, v, max c v r} J B τ) n).Additive := Functor.additive_of_iso ei
  let e := (NatIso.mapHomologicalComplex ei (.up ℤ)).app P
  exact ⟨SheafOfModules.kFlat_iso_independent (B n) e.symm h.1,
    fun i ↦ SheafOfModules.flatOnSite_of_iso (B n)
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso e.symm) (h.2 i)⟩

private theorem quotientEvaluation_tensor (A : Data.{c, v, r} J B τ)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) (n : ℕ) :
    IsIso ((A.tensorEvaluationModel n).chain P Q) := by
  let K := coefficientSequenceTopology J
  let S := systemRing.{c, v, max c v r} J B τ
  let F := evaluation.{c, v, max c v r} J B τ n
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B n)
  let := SheafOfModules.monoidalCategory (B n)
  let tower := rings.{c, v, max c v r} J B τ
  let L := SheafOfModules.systemEvaluation tower n
  have : PreservesColimitsOfSize.{0, 0} L :=
    ⟨fun {D} _ ↦ SheafOfModules.systemEvaluation_colimitsOfShape tower D n⟩
  let E := SheafOfModules.strictSystemSequenceEquivalence tower
  have : E.inverse.IsEquivalence := E.isEquivalence_inverse
  have : PreservesColimitsOfSize.{0, 0} E.inverse := inferInstance
  have hcomp : PreservesColimitsOfSize.{0, 0} (E.inverse ⋙ L) :=
    comp_preservesColimits E.inverse L
  have he : F = E.inverse ⋙ L := by
    rw [show F = SheafOfModules.systemSequenceEvaluation tower n from
      quotientEvaluation_eq.{c, v, r} J B τ n]
    rfl
  have : PreservesColimitsOfSize.{0, 0} F := he.symm ▸ hcomp
  let m := A.tensorEvaluationModel n
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  have (i : ℤ) : IsIso ((m.chain P Q).f i) := by
    let colim := HomologicalComplex.mapBifunctor.isColimitMapCofan
      (G := F) (F := curriedTensor _) (c := ComplexShape.up ℤ) P Q i
    let t := Cofan.IsColimit.desc colim
      (fun x ↦ (m.ordinary (P.X x.1.1) (Q.X x.1.2)).hom ≫
        tensorSummand.{c, v, r} J (B n) FP FQ x.1.1 x.1.2 i x.2)
    have ht (a b : ℤ) (h : a + b = i) :
        F.map (tensorSummand.{c, v, r} K S P Q a b i h) ≫ t =
          (m.ordinary (P.X a) (Q.X b)).hom ≫
            tensorSummand.{c, v, r} J (B n) FP FQ a b i h :=
      Cofan.IsColimit.fac colim _ ⟨⟨a, b⟩, h⟩
    refine ⟨t, ?_, ?_⟩
    · apply HomologicalComplex.mapBifunctor.hom_ext
      intro a b h
      change tensorSummand.{c, v, r} J (B n) FP FQ a b i h ≫
        (m.chain P Q).f i ≫ t = _
      rw [← Category.assoc, m.summand, Category.assoc, ht,
        Iso.inv_hom_id_assoc]
      rfl
    · apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
      intro a b h
      change F.map (tensorSummand.{c, v, r} K S P Q a b i h) ≫
        (t ≫ (m.chain P Q).f i) = _
      rw [← Category.assoc, ht, Category.assoc, m.summand,
        Iso.hom_inv_id_assoc]
      rfl
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem quotientEvaluation_carrier (n : ℕ)
    (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ) :
    (↑(((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) : Type (max c v r)) =
      ↑(M.val.obj (op (n, U.unop))) := by
  unfold evaluation
  rfl

private theorem quotient_heq_apply
    {X X' : Type a} {Y Y' : Type b} {f : X → Y} {g : X' → Y'}
    (hY : Y = Y') (hf : HEq f g) {x : X} {x' : X'} (hx : HEq x x') :
    HEq (f x) (g x') := by
  cases hY
  exact heq_of_eq (congr_heq hf hx)

/-- Simultaneous quotient reduction models in the ordinary derived category of whole
semilinear systems, with all normalized representative comparisons.
Source: Stacks 06YS, 0G7E, 06YY, 07A2, 06YP; agent whole-system refinement
(blueprint: lem-pur-quotient-system-flat-models).
Proof:
1. Construct normalized scalar data from the existing SystemScalarModel, for the
   whole quotient ring map and for every coefficient level. The ordinary vertical
   slice comparison and its unit normalization give reductionEvaluation and evaluation_unit.
2. Pull back along the geometric sequence projection to obtain a K-flat constant
   complex with flat terms. Scalar extension along the quotient map preserves these
   properties; exact evaluation gives level_good.
3. The normalized scalar model preserves quasi-isomorphisms between these complexes
   and its counit is invertible on them. Exact evaluation gives quasiIso.
4. Unit naturality along each horizontal arrow gives reduction_transition: the
   constant input restricts by the identity, and the recorded transition evaluates
   the actual restriction on the scalar extension.
5. The fixed-factor clauses of the signed total-tensor cone theorem preserve
   quasi-isomorphisms in either K-flat factor. Compose them, then evaluate.
6. Evaluation preserves the direct sums defining total tensor. The ordinary tensor
   comparison and its inverse induce inverse maps on every degree by their summand
   equations, proving that the recorded chain comparison is invertible. -/
theorem quotientSystemFlatModels (A : Data.{c, v, r} J B τ) :
    Nonempty (QuotientSystemFlatModels.{c, v, r} J R B τ α hα A) := by
  classical
  obtain ⟨S⟩ := quotientScalar_exists.{c, v, r} (coefficientSequenceTopology J)
    (quotientRingMap.{c, v, r} J R B τ α hα)
  have levelsExist (n : ℕ) : Nonempty (ScalarData.{c, v, max c v r} (α n)) :=
    quotientScalar_exists.{c, v, r} J (α n)
  let levels (n : ℕ) := (levelsExist n).some
  obtain ⟨ev, hu⟩ := quotientOrdinaryModels.{c, v, r} J R B τ α hα S levels
  let Δ := (quotientConstant.{c, v, r} J R).mapHomologicalComplex (.up ℤ)
  let F := quotientReduction.{c, v, r} J R B τ α hα S
  have good (P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) (fP : flatTerms.{c, v, r} J R P) :
      (F.obj P).IsKFlatIndependentCoefficients ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) (F.obj P) := by
    have hc := quotientConstant_preservesGood.{c, v, r} J R P hP fP
    exact quotientScalar_good.{c, v, r} (coefficientSequenceTopology J)
      (quotientRingMap.{c, v, r} J R B τ α hα) S (Δ.obj P) hc.1 hc.2
  have preserves {P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ}
      (f : P ⟶ Q) (hP : P.IsKFlatIndependentCoefficients)
      (fP : flatTerms.{c, v, r} J R P) (hQ : Q.IsKFlatIndependentCoefficients)
      (fQ : flatTerms.{c, v, r} J R Q) (hf : QuasiIso f) : QuasiIso (F.map f) := by
    have := hf
    exact S.model.preserves (Δ.map f)
      (quotientConstant_preservesGood.{c, v, r} J R P hP fP).1
      (quotientConstant_preservesGood.{c, v, r} J R Q hQ fQ).1 (by infer_instance)
  refine ⟨{
    scalar := S
    levels := levels
    reductionEvaluation := ev
    evaluation_unit := hu
    reduction_transition := ?_
    good := good
    level_good := ?_
    quasiIso := ?_
    computes := ?_
    tensor_quasiIso := ?_
    tensor_level := ?_ }⟩
  · intro M n U x y hy
    have ht := (transition_exists.{c, v, max c v r} J B τ
      (Nat.le_succ n)).exists.choose_spec
        (S.model.E.obj ((quotientConstant.{c, v, r} J R).obj M)) U
    have hn := quotientEvaluation_carrier.{c, v, r} J B τ n
      (S.model.E.obj ((quotientConstant.{c, v, r} J R).obj M)) U
    have hh := quotient_heq_apply hn ht hy
    refine hh.trans (heq_of_eq ?_)
    rw [quotientScalar_section.{c, v, r}, quotientScalar_section.{c, v, r}]
    let d := (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op
    have hc : ((quotientConstant.{c, v, r} J R).obj M).val.map d x = x := by
      change M.val.presheaf.map (𝟙 U) x = x
      rw [M.val.presheaf.map_id]
      rfl
    have h := (PresheafOfModules.naturality_apply
      (S.ordinaryAdjunction.unit.app ((quotientConstant.{c, v, r} J R).obj M)).val d x).symm
    change (S.model.E.obj ((quotientConstant.{c, v, r} J R).obj M)).val.map d
      ((S.ordinaryAdjunction.unit.app ((quotientConstant.{c, v, r} J R).obj M)).val.app
        (op (n + 1, U.unop)) x) =
      (S.ordinaryAdjunction.unit.app ((quotientConstant.{c, v, r} J R).obj M)).val.app
        (op (n, U.unop)) (((quotientConstant.{c, v, r} J R).obj M).val.map d x) at h
    rw [hc] at h
    exact h
  · intro P hP fP n
    exact quotientEvaluation_good.{c, v, r} J B τ (F.obj P) (good P hP fP).1 (good P hP fP).2 n
  · intro P Q f hP fP hQ fQ hf n
    have := preserves f hP fP hQ fQ hf
    infer_instance
  · intro P hP fP
    exact S.model.computes (Δ.obj P)
      (quotientConstant_preservesGood.{c, v, r} J R P hP fP).1
  · intro P P' Q Q' f g hP fP hP' fP' hQ fQ hQ' fQ' hf hg n
    let K := coefficientSequenceTopology J
    let T := systemRing.{c, v, max c v r} J B τ
    let := SheafOfModules.isMonoidal_W_independentCoefficients T
    let := SheafOfModules.monoidalCategory T
    let := SheafOfModules.symmetricCategory T
    let native : Abelian (Systems.{c, v, max c v r} J B τ) := inferInstance
    let : Abelian (Systems.{c, v, max c v r} J B τ) :=
      { native with toPreadditive := SheafOfModules.instPreadditive _ }
    let V := (curriedTensor (Systems.{c, v, max c v r} J B τ)).map₂CochainComplex
    let tensor := Functor.uncurry.obj V
    have hleft := (SheafOfModules.TotalTensorSigns.Generic.kflat
      (Systems.{c, v, max c v r} J B τ) (F.obj Q) (good Q hQ fQ).1).1
      _ _ (F.map f) (preserves f hP fP hP' fP' hf)
    have hright := (SheafOfModules.TotalTensorSigns.Generic.kflat
      (Systems.{c, v, max c v r} J B τ) (F.obj P') (good P' hP' fP').1).1
      _ _ (F.map g) (preserves g hQ fQ hQ' fQ' hg)
    have hl : QuasiIso (tensor.map (Prod.mkHom (F.map f) (𝟙 (F.obj Q)))) := by
      change QuasiIso ((V.map (F.map f)).app (F.obj Q) ≫
        (V.obj (F.obj P')).map (𝟙 (F.obj Q)))
      rw [(V.obj (F.obj P')).map_id, Category.comp_id]
      exact hleft.2
    have hr : QuasiIso (tensor.map (Prod.mkHom (𝟙 (F.obj P')) (F.map g))) := by
      change QuasiIso ((V.map (𝟙 (F.obj P'))).app (F.obj Q) ≫
        (V.obj (F.obj P')).map (F.map g))
      rw [V.map_id, NatTrans.id_app, Category.id_comp]
      exact hright.1
    have hh : tensor.map (Prod.mkHom (F.map f) (𝟙 (F.obj Q))) ≫
        tensor.map (Prod.mkHom (𝟙 (F.obj P')) (F.map g)) =
        tensor.map (Prod.mkHom (F.map f) (F.map g)) := by
      rw [← tensor.map_comp]
      congr 1
    have htotal : QuasiIso (tensor.map (Prod.mkHom (F.map f) (F.map g))) := by
      rw [← hh]
      infer_instance
    have hrecorded : QuasiIso
        ((totalTensor.{c, v, r} K T).map (Prod.mkHom (F.map f) (F.map g))) := by
      exact htotal
    let := hrecorded
    change QuasiIso (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex
      (.up ℤ)).map ((totalTensor.{c, v, r} K T).map (Prod.mkHom (F.map f) (F.map g))))
    infer_instance
  · intro P Q n
    exact quotientEvaluation_tensor.{c, v, r} J B τ A (F.obj P) (F.obj Q) n

/-- Exact geometric inverse image preserves componentwise quasi-isomorphisms of good
quotient models. Its actual transitions and cochain-map squares are those of G.pull,
normalized by Geometry.ordinaryPullTransition before localization.
Source: Stacks 06YY; Zheng 4.1 (blueprint: lem-pur-quotient-system-flat-models).
Proof: use QuotientSystemFlatModels.quasiIso at every level. The module inverse image
is exact, so its termwise cochain functor preserves quasi-isomorphisms. The normalized
ordinaryPullEvaluation identifies this with evaluation of the whole pulled system.
Localizing G.pull gives quotientInverseImageComparison. Its naturality holds for all
cochain maps. Geometry.ordinaryPullTransition gives u-inverse-image of tau, and its
naturality gives the strict squares before passing to the derived category. -/
theorem quotientSystemInverseImage (A : Data.{c, v, r} J B τ)
    (M : QuotientSystemFlatModels.{c, v, r} J R B τ α hα A)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (G : Geometry.{c, v, r} J B τ A J' uInv uPush adj)
    {P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ} (f : P ⟶ Q)
    (hP : P.IsKFlatIndependentCoefficients) (flatP : flatTerms.{c, v, r} J R P)
    (hQ : Q.IsKFlatIndependentCoefficients) (flatQ : flatTerms.{c, v, r} J R Q)
    (hf : QuasiIso f) : ∀ n : ℕ,
    QuasiIso (((evaluation.{c, v, max c v r} J' G.coefficients G.coefficientTransition
      n).mapHomologicalComplex (.up ℤ)).map
        ((quotientInverseImage.{c, v, r} J R B τ α hα A M.scalar J' uInv uPush adj G).map f)) := by
  intro n
  let f' := (quotientReduction.{c, v, r} J R B τ α hα M.scalar).map f
  have hlevel : QuasiIso
      (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).map f') :=
    M.quasiIso f hP flatP hQ flatQ hf n
  let := hlevel
  let e := NatIso.mapHomologicalComplex (G.ordinaryPullEvaluation n) (.up ℤ)
  have hright : QuasiIso
      (((evaluation.{c, v, max c v r} J B τ n ⋙
        (G.inverseImage n).modules).mapHomologicalComplex (.up ℤ)).map f') := by
    change QuasiIso (((G.inverseImage n).modules.mapHomologicalComplex (.up ℤ)).map
      (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).map f'))
    infer_instance
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality f').symm)).2 hright


end WeilConjectures.SemilinearSections
