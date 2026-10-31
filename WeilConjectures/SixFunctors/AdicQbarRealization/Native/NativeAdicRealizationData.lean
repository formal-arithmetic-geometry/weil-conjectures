/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.CommonStageInclusionTensorComparison
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicConstructibleRealization
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.SixFunctors.RationalTensorRealization.RationalRealizationTensorComparison

/-! # Native ordinary realization tensor and Hom data

Source: Bhatt--Scholze, Definition 6.8.8, Proposition 6.8.14 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Proposition 5.2 and Theorem 7.7.
(blueprint: def-sf-native-adic-realization-data).

The ordinary module presentation retains the native continuous coefficient sheaf.
All tensor and Hom comparisons concern the published raw common-stage operations.

## Main definitions

- `ring`, `modules`: the native coefficient ring and its ordinary modules.
- `ordinary`, `sectionDerived`, `boundedConstructible`: the exact ordinary presentation.
- `At`: symmetric tensor and coefficient-unit data.
- `homComparison`, `HomLaws`: ambient evaluation transpose and its identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

namespace WeilConjectures.AdicQbarRealization

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The actual commutative coefficient sheaf of the ordinary module presentation.
Source: BS 6.8.1--6.8.2 (blueprint: def-sf-native-adic-realization-data). -/
abbrev ring (R : LocallyFiniteAdicRealization.Realization l X) :=
  @LocallyFiniteAdicRealization.ringSheaf l _ X R.commutative

/-- Ordinary modules over the native coefficient ring, with its sectionwise action.
Source: BS 6.8.8 (blueprint: def-sf-native-adic-realization-data). -/
abbrev modules (R : LocallyFiniteAdicRealization.Realization l X) :=
  ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l X R))

/-- Canonical section-module realization; all exactness structures come from R.
Source: BS 6.8.14 (blueprint: def-sf-native-adic-realization-data). -/
def ordinary (R : LocallyFiniteAdicRealization.Realization l X) :
    generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X ⥤
      DerivedCategory (modules l X R) := by
  letI := R.commutative
  letI := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  exact R.J ⋙ (LocallyFiniteAdicRealization.sections l X).mapDerivedCategory

/-- The canonical ordinary presentation of native modules, retaining the ring action.
Source: BS 6.8.1 (blueprint: def-sf-native-adic-realization-data). -/
def sectionFunctor (R : LocallyFiniteAdicRealization.Realization l X) :
    ProEtale.AdicSheaf l X ⥤ modules l X R :=
  @LocallyFiniteAdicRealization.sections l _ X R.commutative

/-- The exact derived presentation of the native module category.
Source: BS 6.8.8 (blueprint: def-sf-native-adic-realization-data). -/
def sectionDerived (R : LocallyFiniteAdicRealization.Realization l X) :
    DerivedCategory (ProEtale.AdicSheaf l X) ⥤ DerivedCategory (modules l X R) := by
  letI := R.commutative
  letI := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  exact (LocallyFiniteAdicRealization.sections l X).mapDerivedCategory

/-- Bounded constructibility in the ordinary presentation. The native predicate is
bounded cohomology and finite locally closed stratifications with locally finite free
restrictions; sectionFunctor is asserted to be an equivalence in SpaceData below.
Source: BS 6.8.8 (blueprint: def-sf-native-adic-realization-data). -/
def boundedConstructible (R : LocallyFiniteAdicRealization.Realization l X) :
    ObjectProperty (DerivedCategory (modules l X R)) := fun K ↦
  ∃ L : DerivedCategory (ProEtale.AdicSheaf l X),
    ProEtale.DerivedCategory.boundedAdicConstructible l X L ∧
      Nonempty ((sectionDerived l X R).obj L ≅ K)

/-- The ambient unbounded module internal Hom, using the recorded K-injective functor.
Source: BS 6.8.15 (blueprint: def-sf-native-adic-realization-data). -/
abbrev ambientHom (R : LocallyFiniteAdicRealization.Realization l X) :=
  derivedInternalHomOfUniverses.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)

/-- Tensor and evaluation comparison data for the specified common-stage realization.
The Hom map below is the closed transpose of realized evaluation.
Source: BS 6.8.14--6.8.15; HRS 5.2
(blueprint: def-sf-native-adic-realization-data). -/
structure At (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] where
  closed : CoefficientClosedStructure (ambientHom l X R)
  models : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R) closed
  symmetry : @SymmetricCategory _ _ closed.monoidal
  coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
    (ProEt.topology X) (ring l X R) closed models symmetry
  tensor : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
    commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
  unit : closed.monoidal.tensorUnit ≅
    (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X)
  associative : ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (tensor.hom.app (A, B)) (𝟙 _)) ≫
        tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
        (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
      (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
        ((ordinary l X R).obj C)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (tensor.hom.app (B, C))) ≫
        tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C))
  left_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom unit.hom (𝟙 _)) ≫
        tensor.hom.app (pullbackTensorCommonUnit l (PadicAlgCl l) X, A) ≫
        (ordinary l X R).map (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.leftUnitor ((ordinary l X R).obj A)).hom
  right_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (𝟙 _) unit.hom) ≫
        tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
        (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom
  symmetric : ∀ A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    tensor.hom.app (A, B) ≫
        (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
      (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
        tensor.hom.app (B, A)
  hom_isIso : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    IsIso (closed.transpose _ _ _
      (tensor.hom.app ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P,
          P.obj.1.unop) ≫
        (ordinary l X R).map ((podCommonClosed l (PadicAlgCl l) X).evaluation P)))

/-- The comparison is defined by transposition, rather than chosen independently.
Source: BS 3.4.11 and 6.8.15
(blueprint: def-sf-native-adic-realization-data). -/
def homComparison (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory) :
    (ordinary l X R).obj ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P) ⟶
      (ambientHom l X R).obj
        (op ((ordinary l X R).obj P.obj.1.unop), (ordinary l X R).obj P.obj.2) :=
  A.closed.transpose _ _ _
    (A.tensor.hom.app ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P,
        P.obj.1.unop) ≫
      (ordinary l X R).map ((podCommonClosed l (PadicAlgCl l) X).evaluation P))

/-- Naturality in both permitted Hom variables, evaluation, and preservation of
transposes for every test object. Naturality includes the finite-field transition
isomorphisms already encoded in the common-stage Hom functor.
Source: BS 3.4.11 and 6.8.15
(blueprint: def-sf-native-adic-realization-data). -/
structure HomLaws (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R) : Prop where
  naturality : ∀ (P Q : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (f : P ⟶ Q),
    (ordinary l X R).map ((commonStageDerivedInternalHom l (PadicAlgCl l) X).map f) ≫
        homComparison l X R A Q =
      homComparison l X R A P ≫ (ambientHom l X R).map
        (Prod.mkHom ((ordinary l X R).map f.hom.1.unop).op
          ((ordinary l X R).map f.hom.2))
  evaluation : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    A.closed.tensor.map (Prod.mkHom (homComparison l X R A P) (𝟙 _)) ≫
        A.closed.evaluation ((ordinary l X R).obj P.obj.1.unop)
          ((ordinary l X R).obj P.obj.2) =
      A.tensor.hom.app ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P,
        P.obj.1.unop) ≫
        (ordinary l X R).map ((podCommonClosed l (PadicAlgCl l) X).evaluation P)
  transpose : ∀ (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
      (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (f : (commonStageDerivedTensor l (PadicAlgCl l) X).obj (L, P.obj.1.unop) ⟶ P.obj.2),
    A.closed.transpose _ _ _ (A.tensor.hom.app (L, P.obj.1.unop) ≫
        (ordinary l X R).map f) =
      (ordinary l X R).map ((podCommonClosed l (PadicAlgCl l) X).transpose L P f) ≫
        homComparison l X R A P

end WeilConjectures.AdicQbarRealization
