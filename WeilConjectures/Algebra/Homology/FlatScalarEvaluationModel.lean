/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ScalarInternalHomAdjunction
public import WeilConjectures.Algebra.Homology.StrictScalarHomChain
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Algebra.Homology.StrictScalarHomChain
import all WeilConjectures.Algebra.Homology.ScalarHomTensorCoherence
import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.RingedTensorComparisonExtension
import all WeilConjectures.Algebra.Homology.ScalarTensorExactRepresentative
import WeilConjectures.Algebra.Homology.ScalarOrdinaryEvaluationResolution
import WeilConjectures.Algebra.Homology.ScalarOrdinaryEvaluationModel
import WeilConjectures.Algebra.Homology.ScalarHomDerivedSquareCoherence
import all WeilConjectures.Algebra.Homology.ScalarOrdinaryEvaluationCoefficientSquare
import all WeilConjectures.Algebra.Homology.ScalarHomComparisonTower
import all WeilConjectures.CategoryTheory.ClosedScalarHomComparison
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Flat scalar evaluation on an arbitrary first complex

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 08J9 and 06YP;
the one-K-flat-factor scalar evaluation refinement recorded in the DAG, rather
than a verbatim assertion of these tags
(blueprint: lem-sfb-hom-flat-scalar-evaluation-model).

All tensors, Hom products, sections and localization functors below are the
recorded constructions. The data asserted to exist are fixed by generator
formulas and the K-flat normalization; no representative is chosen arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxErrors 4
-- Avoid re-synthesizing the site-universe instances in the section-variable linter.
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules WeilConjectures

attribute [local irreducible] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

attribute [local irreducible] derivedInternalHomOfUniverses
  CoefficientClosedStructure.tensor coefficientBaseChangeHom
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors

attribute [local irreducible] homComplex homComplexπ
  RingedDerivedNative.chainEquiv

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  scalarPairComplexComparison CoefficientTensorModels.iso
  SheafOfModules.monoidalCategory homComplexFunctor

namespace CategoryTheory

private theorem scalar_bijection_baseChange
    {A : Type*} {B : Type*} [Category A] [Category B]
    {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
    (m : S.tensor ⋙ F ≅ F.prod F ⋙ T.tensor) (X K L : A) (β : X ⟶ H.obj (op K, L)) :
    (S.transpose (U.obj (F.obj X)) K (U.obj (F.obj L))).symm
        (ClosedScalarHom.bijection S T adj m _ K (F.obj L)
          (U.map (F.map β) ≫ U.map (coefficientBaseChangeHom S T F m K L))) =
      S.tensor.map (Prod.mkHom (𝟙 _) (adj.unit.app K)) ≫
        ClosedScalarHom.restrictionTensor S T adj m (F.obj X) (F.obj K) ≫
        U.map (m.inv.app (X, K)) ≫
        U.map (F.map ((S.transpose X K L).symm β)) := by
  unfold ClosedScalarHom.bijection
  dsimp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  change adj.homEquiv _ _
    (m.hom.app (U.obj (F.obj X), K) ≫
      (T.transpose _ (F.obj K) (F.obj L)).symm
        ((adj.homEquiv _ _).symm
          (U.map (F.map β) ≫ U.map (coefficientBaseChangeHom S T F m K L))) ≫ 𝟙 _) = _
  have hs : (adj.homEquiv _ _).symm
      (U.map (F.map β) ≫ U.map (coefficientBaseChangeHom S T F m K L)) =
        adj.counit.app (F.obj X) ≫ F.map β ≫ coefficientBaseChangeHom S T F m K L := by
    have hh := adj.homEquiv_naturality_right_symm
      (𝟙 (U.obj (F.obj X))) (F.map β ≫ coefficientBaseChangeHom S T F m K L)
    rw [adj.homEquiv_symm_id] at hh
    simpa only [Category.id_comp, Functor.map_comp, Category.assoc] using hh
  rw [hs, scalarUncurry_pre, scalarUncurry_pre, scalarBaseChangeHom_beta]
  have hn := m.inv.naturality (Prod.mkHom β (𝟙 K))
  change T.tensor.map (Prod.mkHom (F.map β) (F.map (𝟙 K))) ≫ m.inv.app (_, K) =
    m.inv.app (X, K) ≫ F.map (S.tensor.map (Prod.mkHom β (𝟙 K))) at hn
  rw [F.map_id] at hn
  simp only [Category.comp_id]
  rw [reassoc_of% hn, Adjunction.homEquiv_unit]
  rw [reassoc_of% ClosedScalarHom.restrictionTensor_unit S T adj m (F.obj X) K]
  rw [scalarUncurry]
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.IsFlatOnSite

namespace CategoryTheory.FlatScalarEvaluation

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J)
  (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    ScalarHomTensorComparison.{c, v, r, w} (J := J) M a)
  (Θ : ScalarInternalHomAdjunction.{c, v, r, w} (J := J) M μ)

/-- Termwise application of the already recorded ordinary extension.
Source: Stacks 07A6 (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
abbrev extension {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :=
  scalarComplex (M.scalar a).extension (M.scalar a).extension_additive

set_option backward.isDefEq.respectTransparency false in
/-- The actual sheafified scalar generator, expressed through the normalized unit.
Source: Stacks 03CZ, 07A6 (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
def extensionSection {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) :
    (((extension M a).obj D).X n).val.obj V :=
  s • scalarHomUnitSection M a (D.X n) V x

/-- The universal derived counit on an actual complex, with no flatness restriction.
Source: Stacks 06YY (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
abbrev representative {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) :=
  scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
    (M.scalar a).derived (M.scalar a).counit D

/-- Exact-extension identification after restriction, using the actual counit.
Its only proof input is invertibility of that very counit, never an arbitrary iso.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
def exactRepresentative {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (h : ∀ D : StrictScalarHom.Complex.{c, v, r} R, IsIso (representative M a D))
    (D : StrictScalarHom.Complex.{c, v, r} R) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj (DerivedCategory.Q.obj D)) ≅
      DerivedCategory.Q.obj ((StrictScalarHom.restriction.{c, v, r} a).obj
        ((extension M a).obj D)) :=
  letI := h D
  (scalarDerivedRestriction a).mapIso (asIso (representative M a D)) ≪≫
    (scalarRestrictionComparison a).app ((extension M a).obj D)

/-- The scalar-unit tensor map is the counit mate of the specified strong comparison.
Source: Stacks 07A4, 07A6 (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
def unitTensor {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (X : DerivedCategory (scalarModules J S)) (K : DerivedCategory (scalarModules J R)) :
    (M.closed R).tensor.obj ((scalarDerivedRestriction a).obj X, K) ⟶
      (scalarDerivedRestriction a).obj
        ((M.closed S).tensor.obj (X, (M.scalar a).derived.obj K)) :=
  (M.closed R).tensor.map (Prod.mkHom (𝟙 _) ((M.scalar a).adjunction.unit.app K)) ≫
    scalarHomRestrictionTensor M a (μ a) X ((M.scalar a).derived.obj K)

/-- Transpose of an evaluated chain map using the one-factor representative comparison.
Source: Stacks 08J9 (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
def transpose {R : Sheaf J CommRingCat.{max c v r}} (D P I : StrictScalarHom.Complex.{c, v, r} R)
    (i : DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (D, P)) ≅
      (M.closed R).tensor.obj (DerivedCategory.Q.obj D, DerivedCategory.Q.obj P))
    (f : (coefficientTotalTensor.{r, c, v} J R).obj (D, P) ⟶ I) :=
  (M.closed R).transpose (DerivedCategory.Q.obj D) (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj I) (i.inv ≫ DerivedCategory.Q.map f)

/-- Transport from the literal scalar tensor representative to restricted derived extension.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
def sourceTransport {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (h : ∀ D : StrictScalarHom.Complex.{c, v, r} R, IsIso (representative M a D))
    (ν : StrictScalarHom.tensor.{c, v, r} a ≅
      extension M a ⋙ StrictScalarHom.restriction.{c, v, r} a)
    (D : StrictScalarHom.Complex.{c, v, r} R) :=
  DerivedCategory.Q.map (ν.hom.app D) ≫ (exactRepresentative M a h D).inv

/-- Scalar extension of an evaluated chain map, with the inverse tensor comparison
and scalar unit, expressed on the literal first-factor representative.
Source: Stacks 07A4, 08J9 (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
def extendedEvaluation {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (h : ∀ D : StrictScalarHom.Complex.{c, v, r} R, IsIso (representative M a D))
    (ν : StrictScalarHom.tensor.{c, v, r} a ≅
      extension M a ⋙ StrictScalarHom.restriction.{c, v, r} a)
    (D P I : StrictScalarHom.Complex.{c, v, r} R)
    (iD : DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (D, P)) ≅
      (M.closed R).tensor.obj (DerivedCategory.Q.obj D, DerivedCategory.Q.obj P))
    (iA : DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj
        ((StrictScalarHom.tensor.{c, v, r} a).obj D, P)) ≅
      (M.closed R).tensor.obj
        (DerivedCategory.Q.obj ((StrictScalarHom.tensor.{c, v, r} a).obj D),
          DerivedCategory.Q.obj P))
    (f : (coefficientTotalTensor.{r, c, v} J R).obj (D, P) ⟶ I) :=
  iA.hom ≫ (M.closed R).tensor.map
      (Prod.mkHom (sourceTransport M a h ν D) (𝟙 (DerivedCategory.Q.obj P))) ≫
    unitTensor M μ a ((M.scalar a).derived.obj (DerivedCategory.Q.obj D))
      (DerivedCategory.Q.obj P) ≫
    (scalarDerivedRestriction a).map ((μ a).iso.inv.app
      (DerivedCategory.Q.obj D, DerivedCategory.Q.obj P)) ≫
    (scalarDerivedRestriction a).map ((M.scalar a).derived.map
      (iD.inv ≫ DerivedCategory.Q.map f)) ≫ (exactRepresentative M a h I).hom

/-- The Theta U(c) transpose in exactly the same source and target representatives.
The comparison c is the recorded evaluation-defined coefficientBaseChangeHom.
Source: Stacks 07A4, 08J9 (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
def adjunctionEvaluation {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (h : ∀ D : StrictScalarHom.Complex.{c, v, r} R, IsIso (representative M a D))
    (ν : StrictScalarHom.tensor.{c, v, r} a ≅
      extension M a ⋙ StrictScalarHom.restriction.{c, v, r} a)
    (D P I : StrictScalarHom.Complex.{c, v, r} R)
    (iD : DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (D, P)) ≅
      (M.closed R).tensor.obj (DerivedCategory.Q.obj D, DerivedCategory.Q.obj P))
    (iA : DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj
        ((StrictScalarHom.tensor.{c, v, r} a).obj D, P)) ≅
      (M.closed R).tensor.obj
        (DerivedCategory.Q.obj ((StrictScalarHom.tensor.{c, v, r} a).obj D),
          DerivedCategory.Q.obj P))
    (f : (coefficientTotalTensor.{r, c, v} J R).obj (D, P) ⟶ I) :=
  iA.hom ≫ (M.closed R).tensor.map
      (Prod.mkHom (sourceTransport M a h ν D) (𝟙 (DerivedCategory.Q.obj P))) ≫
    ((M.closed R).transpose _ (DerivedCategory.Q.obj P)
      ((scalarDerivedRestriction a).obj
        ((M.scalar a).derived.obj (DerivedCategory.Q.obj I)))).symm
      ((scalarDerivedRestriction a).map ((M.scalar a).derived.map (transpose M D P I iD f)) ≫
        (scalarDerivedRestriction a).map
          (coefficientBaseChangeHom (M.closed R) (M.closed S) (M.scalar a).derived
            (μ a).iso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)) ≫
        (Θ.iso a).hom.app
          (op (DerivedCategory.Q.obj P), (M.scalar a).derived.obj (DerivedCategory.Q.obj I))) ≫
    (exactRepresentative M a h I).hom

/-- Canonical derived extension transport for the two paths of a commuting square.
The equality of composite ring maps is transported before the inverse composition iso.
Source: Stacks 0D6D (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
def squareTransport {R S R' S' : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (a : R ⟶ R') (d : S ⟶ S') (φ' : R' ⟶ S')
    (h : φ ≫ d = a ≫ φ') :
    (M.scalar φ).derived ⋙ (M.scalar d).derived ≅
      (M.scalar a).derived ⋙ (M.scalar φ').derived :=
  scalarHomExtensionComp M φ d ≪≫
    eqToIso (congrArg (fun z ↦ (M.scalar z).derived) h) ≪≫
    (scalarHomExtensionComp M a φ').symm

attribute [local irreducible] extendedEvaluation adjunctionEvaluation unitTensor
  sourceTransport exactRepresentative

/-- The ordinary part of the recorded scalar data, with all normalizations retained.
Source: Stacks 07A6 (blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
@[no_expose] private abbrev ordinaryScalars :
    ScalarOrdinaryEvaluation.Scalars.{c, v, r} (J := J) where
  E := fun a ↦ (M.scalar a).extension
  additive := fun a ↦ (M.scalar a).extension_additive
  obj_eq := fun a ↦ (M.scalar a).extension_obj
  map_eq := fun a ↦ (M.scalar a).extension_map
  adj := fun a ↦ (M.scalar a).ordinaryAdjunction
  unit_pure := fun a ↦ (M.scalar a).ordinaryUnit

/-- Representatives packages the displayed normalized maps or equations.
Source: Stacks 07A4, 08J9, 06YP and the DAG refinement
(blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
structure Representatives where
  /-- Canonical S tensor D = UED before localization. -/
  nu : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    StrictScalarHom.tensor.{c, v, r} a ≅
      extension M a ⋙ StrictScalarHom.restriction.{c, v, r} a
  /-- The isomorphism is identity on sheafification-unit generators. -/
  nu_pure : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V),
    (((nu a).hom.app D).f n).val.app V
      (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) =
        extensionSection M a D n V s x
  /-- Exactness makes the canonical comparison invertible on every unbounded complex. -/
  exact_computes : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ D : StrictScalarHom.Complex.{c, v, r} R, IsIso (representative M a D)
  /-- A single K-flat second factor computes tensor against every first complex. -/
  tensorIso : ∀ {R : Sheaf J CommRingCat.{max c v r}} (P : StrictScalarHom.Complex.{c, v, r} R),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    ∀ D : StrictScalarHom.Complex.{c, v, r} R,
      DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (D, P)) ≅
        (M.closed R).tensor.obj (DerivedCategory.Q.obj D, DerivedCategory.Q.obj P)
  /-- Agreement with the existing representative comparison, without a new normalization. -/
  tensorIso_normalization : ∀ {R : Sheaf J CommRingCat.{max c v r}}
    (P D : StrictScalarHom.Complex.{c, v, r} R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hp : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hD : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) D),
    tensorIso P hP hp D =
      CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R) D P hD hP
  /-- Naturality for arbitrary chain maps in the first complex. -/
  tensorIso_natural : ∀ {R : Sheaf J CommRingCat.{max c v r}}
    (P D D' : StrictScalarHom.Complex.{c, v, r} R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hp : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) (t : D' ⟶ D),
    DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom t (𝟙 P))) ≫ (tensorIso P hP hp D).hom =
      (tensorIso P hP hp D').hom ≫ (M.closed R).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map t) (𝟙 (DerivedCategory.Q.obj P)))
  /-- Actual chain evaluation, before making any resolution or flatness assumptions. -/
  evaluate : ∀ {R : Sheaf J CommRingCat.{max c v r}} (P I D : StrictScalarHom.Complex.{c, v, r} R)
    (_b : D ⟶ homComplex (R := R) P I),
    (coefficientTotalTensor.{r, c, v} J R).obj (D, P) ⟶ I
  /-- Each homogeneous summand is evaluated in the actual product Hom coordinate. -/
  evaluate_pure : ∀ {R : Sheaf J CommRingCat.{max c v r}}
    (P I D : StrictScalarHom.Complex.{c, v, r} R)
    (b : D ⟶ homComplex (R := R) P I) (n i k : ℤ) (h : n + i = k) (h' : i + n = k)
    (V : Cᵒᵖ) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V),
    ((evaluate P I D b).f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p) =
        StrictScalarHom.evaluate.{c, v, r} P I n i k h' V ((b.f n).val.app V x) p
  /-- Actual scalar chain evaluation on (S tensor D) tensor P. -/
  scalarEvaluate : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (_b : D ⟶ homComplex (R := R) P I),
    (coefficientTotalTensor.{r, c, v} J R).obj
      ((StrictScalarHom.tensor.{c, v, r} a).obj D, P) ⟶
        (StrictScalarHom.restriction.{c, v, r} a).obj ((extension M a).obj I)
  /-- h_b((s tensor x) tensor p) = s tensor b(x)(p), for actual local generators. -/
  scalarEvaluate_pure : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (b : D ⟶ homComplex (R := R) P I)
    (n i k : ℤ) (h : n + i = k) (h' : i + n = k) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V),
    ((scalarEvaluate a P I D b).f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J R
        ((StrictScalarHom.tensor.{c, v, r} a).obj D) P n i k h V
        (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p) =
      extensionSection M a I k V s
        (StrictScalarHom.evaluate.{c, v, r} P I n i k h' V ((b.f n).val.app V x) p)
  /-- Scalar-unit insertion on the actual tensor complexes, without deriving them. -/
  chainUnitTensor : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (V P : StrictScalarHom.Complex.{c, v, r} R),
    (coefficientTotalTensor.{r, c, v} J R).obj
      ((StrictScalarHom.restriction.{c, v, r} a).obj ((extension M a).obj V), P) ⟶
    (StrictScalarHom.restriction.{c, v, r} a).obj
      ((coefficientTotalTensor.{r, c, v} J S).obj
        ((extension M a).obj V, (extension M a).obj P))
  /-- The unit insertion sends y tensor p to y tensor (1 tensor p). -/
  chainUnitTensor_pure : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D P : StrictScalarHom.Complex.{c, v, r} R) (n i k : ℤ) (h : n + i = k) (V : Cᵒᵖ)
    (y : (((extension M a).obj D).X n).val.obj V) (p : (P.X i).val.obj V),
    ((chainUnitTensor a D P).f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J R
        ((StrictScalarHom.restriction.{c, v, r} a).obj ((extension M a).obj D)) P
        n i k h V y p) =
      coefficientTensorGenerator.{r, c, v} J S ((extension M a).obj D)
        ((extension M a).obj P) n i k h V y (extensionSection M a P i V 1 p)


/-- The three derived and descent equations for the same actual representatives.
Source: Stacks 07A4, 08J9, 06YP and the DAG refinement
(blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
structure Calculation (E : Representatives M) : Prop where
  /-- The scalar-extended evaluation composite is represented by this actual h_b. -/
  derived_formula : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (ha : PreservesFiniteLimits (M.scalar a).extension)
    (P I D : StrictScalarHom.Complex.{c, v, r} R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hp : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (_hI : I.IsKInjective) (b : D ⟶ homComplex (R := R) P I),
    extendedEvaluation M μ a (E.exact_computes a ha) (E.nu a) D P I
      (E.tensorIso P hP hp D) (E.tensorIso P hP hp ((StrictScalarHom.tensor.{c, v, r} a).obj D))
      (E.evaluate P I D b) = DerivedCategory.Q.map (E.scalarEvaluate a P I D b)
  /-- The normalized scalar Hom adjunction has exactly that same derived transpose. -/
  adjunction_formula : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (ha : PreservesFiniteLimits (M.scalar a).extension)
    (P I D : StrictScalarHom.Complex.{c, v, r} R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hp : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (_hI : I.IsKInjective) (b : D ⟶ homComplex (R := R) P I),
    adjunctionEvaluation M μ Θ a (E.exact_computes a ha) (E.nu a) D P I
      (E.tensorIso P hP hp D) (E.tensorIso P hP hp ((StrictScalarHom.tensor.{c, v, r} a).obj D))
      (E.evaluate P I D b) = DerivedCategory.Q.map (E.scalarEvaluate a P I D b)
  /-- Descent for every resolution: all cancellation maps are quasi-isomorphisms,
  and the representative square gives the same actual chain map after precomposition. -/
  resolution : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (_ha : PreservesFiniteLimits (M.scalar a).extension)
    (P I D V : StrictScalarHom.Complex.{c, v, r} R)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (_hp : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (_hI : I.IsKInjective) (b : D ⟶ homComplex (R := R) P I)
    (t : V ⟶ D) (_hV : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) V)
    (_hv : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (V.X n)) (_ht : QuasiIso t),
    QuasiIso ((extension M a).map t) ∧
    QuasiIso ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom t (𝟙 P))) ∧
    QuasiIso ((extension M a).map
      ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom t (𝟙 P)))) ∧
    QuasiIso ((coefficientTotalTensor.{r, c, v} J R).map
      (Prod.mkHom ((StrictScalarHom.tensor.{c, v, r} a).map t) (𝟙 P))) ∧
    (coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom ((StrictScalarHom.tensor.{c, v, r} a).map t) (𝟙 P)) ≫
          E.scalarEvaluate a P I D b =
      (coefficientTotalTensor.{r, c, v} J R).map
          (Prod.mkHom ((E.nu a).hom.app V) (𝟙 P)) ≫
        E.chainUnitTensor a V P ≫
        (StrictScalarHom.restriction.{c, v, r} a).map ((μ a).complexIso V P).inv ≫
        (StrictScalarHom.restriction.{c, v, r} a).map
          ((extension M a).map (E.evaluate P I V (t ≫ b)))


/-- ChainPresentation packages the displayed normalized maps or equations.
Source: Stacks 07A4, 08J9, 06YP and the DAG refinement
(blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
structure ChainPresentation where
  /-- The existing strict scalar-Hom data, used for coefficient transports only. -/
  chainData : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    StrictScalarHom.Data.{c, v, r} a
  /-- Identify its ordinary extension with the specified scalar pair termwise. -/
  chainIso : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    (chainData a).extension.complex ≅ extension M a
  /-- This bridge is the identity on sheafified generators, so no twist is admitted. -/
  chainIso_pure : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V),
    ((((chainIso a).hom.app D).f n).val.app V)
      ((chainData a).extension.section D n V s x) = extensionSection M a D n V s x


/-- Compatibility of the actual h maps with every normalized coefficient square.
Source: Stacks 07A4, 08J9, 06YP and the DAG refinement
(blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
def ChainSquare (E : Representatives.{c, v, r, w} (J := J) M) (B : ChainPresentation.{c, v, r, w}
  (J := J) M) : Prop :=
  ∀ {R S R' S' : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (a : R ⟶ R') (d : S ⟶ S') (φ' : R' ⟶ S')
    (_h : φ ≫ d = a ≫ φ'),
    ∃ Q : StrictScalarHom.CoefficientSquare.{c, v, r}
      (B.chainData φ) (B.chainData a) (B.chainData d) (B.chainData φ'),
      StrictScalarHom.CoefficientCompatibility.{c, v, r} Q ∧
      ∀ (P I D : StrictScalarHom.Complex.{c, v, r} R) (b : D ⟶ homComplex (R := R) P I),
      (B.chainIso a).hom.app ((coefficientTotalTensor.{r, c, v} J R).obj
          ((StrictScalarHom.tensor.{c, v, r} φ).obj D, P)) ≫
        ((μ a).complexIso ((StrictScalarHom.tensor.{c, v, r} φ).obj D) P).hom ≫
        (coefficientTotalTensor.{r, c, v} J R').map
          (Prod.mkHom ((B.chainIso a).inv.app ((StrictScalarHom.tensor.{c, v, r} φ).obj D))
            ((B.chainIso a).inv.app P)) ≫
        (coefficientTotalTensor.{r, c, v} J R').map
          (Prod.mkHom (Q.tensorComparison D) (𝟙 ((B.chainData a).extension.complex.obj P))) ≫
        E.scalarEvaluate φ' ((B.chainData a).extension.complex.obj P)
          ((B.chainData a).extension.complex.obj I) ((B.chainData a).extension.complex.obj D)
          ((B.chainData a).extension.complex.map b ≫ (B.chainData a).homComparison P I) ≫
        (StrictScalarHom.restriction.{c, v, r} φ').map
          ((B.chainIso φ').inv.app ((B.chainData a).extension.complex.obj I)) =
      (B.chainData a).extension.complex.map
          (E.scalarEvaluate φ P I D b ≫
            (StrictScalarHom.restriction.{c, v, r} φ).map ((B.chainIso φ).inv.app I)) ≫
        Q.restrictionMate.app ((B.chainData φ).extension.complex.obj I) ≫
        (StrictScalarHom.restriction.{c, v, r} φ').map (Q.extensionIso.hom.app I)


/-- DerivedCoherence packages the displayed normalized maps or equations.
Source: Stacks 07A4, 08J9, 06YP and the DAG refinement
(blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
structure DerivedCoherence : Prop where
  /-- Naturality in all derived maps, so inverse localized quasi-isomorphisms are included. -/
  naturality : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (K L K' L' : DerivedCategory (scalarModules J R)) (f : K' ⟶ K) (g : L ⟶ L'),
    (M.scalar a).derived.map
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom f.op g)) ≫
        coefficientBaseChangeHom (M.closed R) (M.closed S) (M.scalar a).derived
          (μ a).iso K' L' =
      coefficientBaseChangeHom (M.closed R) (M.closed S) (M.scalar a).derived
          (μ a).iso K L ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J S).map
          (Prod.mkHom ((M.scalar a).derived.map f).op ((M.scalar a).derived.map g))
  /-- Coefficient towers with the canonical transports on source and both Hom inputs. -/
  composition : ∀ {R S T : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ T)
    (K L : DerivedCategory (scalarModules J R)),
    (M.scalar b).derived.map
        (coefficientBaseChangeHom (M.closed R) (M.closed S) (M.scalar a).derived
          (μ a).iso K L) ≫
      coefficientBaseChangeHom (M.closed S) (M.closed T) (M.scalar b).derived
        (μ b).iso ((M.scalar a).derived.obj K) ((M.scalar a).derived.obj L) ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J T).map
        (Prod.mkHom ((scalarHomExtensionComp M a b).inv.app K).op
          ((scalarHomExtensionComp M a b).hom.app L)) =
      (scalarHomExtensionComp M a b).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
        coefficientBaseChangeHom (M.closed R) (M.closed T) (M.scalar (a ≫ b)).derived
          (μ (a ≫ b)).iso K L
  /-- The identity coefficient map is identity under the canonical scalar unitor. -/
  identity : ∀ (R : Sheaf J CommRingCat.{max c v r})
    (K L : DerivedCategory (scalarModules J R)),
    coefficientBaseChangeHom (M.closed R) (M.closed R) (M.scalar (𝟙 R)).derived
        (μ (𝟙 R)).iso K L ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom ((scalarHomExtensionId M R).inv.app K).op
          ((scalarHomExtensionId M R).hom.app L)) =
      (scalarHomExtensionId M R).hom.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))
  /-- The derived square, with the same source and two Hom-input transports.
  Its two paths are the successive evaluation comparisons, rather than arbitrary maps. -/
  derived_square : ∀ {R S R' S' : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (a : R ⟶ R') (d : S ⟶ S') (φ' : R' ⟶ S')
    (h : φ ≫ d = a ≫ φ') (K L : DerivedCategory (scalarModules J R)),
    (M.scalar d).derived.map
        (coefficientBaseChangeHom (M.closed R) (M.closed S) (M.scalar φ).derived
          (μ φ).iso K L) ≫
      coefficientBaseChangeHom (M.closed S) (M.closed S') (M.scalar d).derived
        (μ d).iso ((M.scalar φ).derived.obj K) ((M.scalar φ).derived.obj L) ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J S').map
        (Prod.mkHom ((squareTransport M φ a d φ' h).inv.app K).op
          ((squareTransport M φ a d φ' h).hom.app L)) =
      (squareTransport M φ a d φ' h).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
        (M.scalar φ').derived.map
          (coefficientBaseChangeHom (M.closed R) (M.closed R') (M.scalar a).derived
            (μ a).iso K L) ≫
        coefficientBaseChangeHom (M.closed R') (M.closed S') (M.scalar φ').derived
          (μ φ').iso ((M.scalar a).derived.obj K) ((M.scalar a).derived.obj L)


attribute [local irreducible] ChainSquare


/-- All clauses of flat scalar evaluation, using the same chain maps throughout.
Source: Stacks 07A4, 08J9, 06YP and the DAG refinement
(blueprint: lem-sfb-hom-flat-scalar-evaluation-model). -/
structure Model where
  /-- Actual generator-normalized representatives. -/
  representatives : Representatives M
  /-- Their derived evaluation, adjunction and resolution-descent equations. -/
  calculation : Calculation M μ Θ representatives
  /-- Existing strict coefficient data with their canonical ordinary-extension bridges. -/
  chain : ChainPresentation M
  /-- The two actual chain routes agree for every compatible coefficient square. -/
  chain_square : ChainSquare M μ representatives chain
  /-- Naturality, coefficient composition, identity and compatible derived squares. -/
  coherence : DerivedCoherence M μ

@[no_expose] private def ordinaryRepresentative
    (E : Representatives.{c, v, r, w} (J := J) M) :
    ScalarOrdinaryEvaluation.RepresentativeData.{c, v, r} (J := J)
      (ordinaryScalars.{c, v, r, w} (J := J) M) where
  nu := E.nu
  nu_pure := E.nu_pure
  evaluate := E.evaluate
  evaluate_pure := E.evaluate_pure
  scalarEvaluate := E.scalarEvaluate
  scalarEvaluate_pure := E.scalarEvaluate_pure
  chainUnitTensor := E.chainUnitTensor
  chainUnitTensor_pure := E.chainUnitTensor_pure

attribute [local irreducible] scalarHomExtensionComp scalarHomExtensionId
attribute [local instance] ScalarDerivedPair.extension_additive

private theorem exact_comparison :
    ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    PreservesFiniteLimits (M.scalar a).extension →
    ∀ D : StrictScalarHom.Complex.{c, v, r} R,
      IsIso (representative.{c, v, r, w} (J := J) M a D) := by
  intro R S a ha D
  let := ha
  let := ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).ordinaryAdjunction.isLeftAdjoint
  obtain ⟨P, t, hp, _, ht, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients D
  let := ht
  have : IsIso (representative.{c, v, r, w} (J := J) M a P) := ((ScalarHomModels.scalar.{c, v, r,
    w} (J := J) M) a).computes P hp
  have hn := (ScalarHomTensor.pairComparison (J := J) M a).naturality t
  rw [ScalarHomTensor.pairComparison_app, ScalarHomTensor.pairComparison_app] at hn
  change ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.map (DerivedCategory.Q.map
    t) ≫ representative.{c, v, r, w} (J := J) M a D =
    representative.{c, v, r, w} (J := J) M a P ≫ DerivedCategory.Q.map ((extension.{c, v, r, w} (J
      := J) M a).map t) at hn
  have : QuasiIso ((extension.{c, v, r, w} (J := J) M a).map t) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology t ((ScalarHomModels.scalar.{c, v, r, w}
      (J := J) M) a).extension
  have : IsIso (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.map
    (DerivedCategory.Q.map t) ≫
      representative.{c, v, r, w} (J := J) M a D) := by rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_left (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.map
    (DerivedCategory.Q.map t)) _


private theorem derived_coherence : DerivedCoherence.{c, v, r, w} (J := J) M μ := by
  have h := ScalarHomDerivedCoherence.coherence.{c, v, r, w} (J := J) M μ
  exact ⟨h.naturality, h.composition, h.identity, h.derived_square⟩

@[no_expose] private def ordinaryTensor :
    ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarOrdinaryEvaluation.Tensor.{c, v, r} (J := J) (ordinaryScalars.{c, v, r, w} (J := J) M)
        a := by
  intro R S a
  exact { complexIso := (μ a).complexIso, generators := (μ a).generators }

@[no_expose] private def ordinaryData : ScalarOrdinaryEvaluation.Construction.{c, v, r} (J := J)
  (ordinaryScalars.{c, v, r, w} (J := J) M) :=
  Classical.choice (ScalarOrdinaryEvaluation.construction_exists.{c, v, r} (J := J)
    (ordinaryScalars.{c, v, r, w} (J := J) M)
    (ordinaryTensor.{c, v, r, w} (J := J) M μ))

attribute [local irreducible] ordinaryData

@[no_expose] private def chainPresentation : ChainPresentation.{c, v, r, w} (J := J) M :=
  let B := (ordinaryData.{c, v, r, w} (J := J) M μ).presentation
  ⟨B.chainData, B.chainIso, B.chainIso_pure⟩

private theorem tensorComparison_inv_pure {R S : Sheaf J CommRingCat.{max c v r}}
    (a : R ⟶ S) (D P : StrictScalarHom.Complex.{c, v, r} R)
    (n i k : ℤ) (h : n + i = k) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V) :
    (((μ a).complexIso D P).inv.f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J S ((extension.{c, v, r, w} (J := J) M a).obj D)
        ((extension.{c, v, r, w} (J := J) M a).obj P) n i k h V
        (extensionSection.{c, v, r, w} (J := J) M a D n V s x) (extensionSection.{c, v, r, w} (J
          := J) M a P i V 1 p)) =
      extensionSection.{c, v, r, w} (J := J) M a ((coefficientTotalTensor.{r, c, v} J R).obj (D,
        P)) k V s
        (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p) := by
  simpa only [extensionSection, one_smul] using
    ScalarTensorRepresentative.tensorComparison_inv_pure (J := J) M μ a D P n i k h V s x p

private theorem scalar_chain_formula (E : Representatives.{c, v, r, w} (J := J) M)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (b : D ⟶ homComplex (R := R) P I) :
    (coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom ((E.nu a).hom.app D) (𝟙 P)) ≫
      E.chainUnitTensor a D P ≫
      (StrictScalarHom.restriction.{c, v, r} a).map ((μ a).complexIso D P).inv ≫
      (StrictScalarHom.restriction.{c, v, r} a).map
        ((extension.{c, v, r, w} (J := J) M a).map (E.evaluate P I D b)) = E.scalarEvaluate a P I
          D b := by
  exact ScalarOrdinaryEvaluation.evaluation_composite.{c, v, r} (J := J)
    (ordinaryScalars.{c, v, r, w} (J := J) M) (ordinaryTensor.{c, v, r, w} (J := J) M μ)
    (ordinaryRepresentative.{c, v, r, w} (J := J) M E) a P I D b

@[no_expose] private def representatives : Representatives.{c, v, r, w} (J := J) M := by
  classical
  let T (R : Sheaf J CommRingCat.{max c v r}) :=
    (ringedTensorComparison_extension.{c, v, r, w} J R ((ScalarHomModels.closed.{c, v, r, w} (J :=
      J) M) R) ((ScalarHomModels.model.{c, v, r, w} (J := J) M) R)).choose
  have hT (R : Sheaf J CommRingCat.{max c v r}) :=
    (ringedTensorComparison_extension.{c, v, r, w} J R ((ScalarHomModels.closed.{c, v, r, w} (J :=
      J) M) R) ((ScalarHomModels.model.{c, v, r, w} (J := J) M) R)).choose_spec
  refine {
    nu := (ordinaryData.{c, v, r, w} (J := J) M μ).nu
    nu_pure := (ordinaryData.{c, v, r, w} (J := J) M μ).nu_pure
    evaluate := (ordinaryData.{c, v, r, w} (J := J) M μ).evaluate
    evaluate_pure := (ordinaryData.{c, v, r, w} (J := J) M μ).evaluate_pure
    scalarEvaluate := (ordinaryData.{c, v, r, w} (J := J) M μ).scalarEvaluate
    scalarEvaluate_pure := (ordinaryData.{c, v, r, w} (J := J) M μ).scalarEvaluate_pure
    chainUnitTensor := (ordinaryData.{c, v, r, w} (J := J) M μ).chainUnitTensor
    chainUnitTensor_pure := (ordinaryData.{c, v, r, w} (J := J) M μ).chainUnitTensor_pure
    exact_computes := exact_comparison.{c, v, r, w} (J := J) M
    tensorIso := fun {R} P hP _ D ↦ T R D P (Or.inr hP)
    tensorIso_normalization := ?_
    tensorIso_natural := ?_
 }
  · intro R P D hP hp hD
    exact (hT R).1 D P hD hP
  · intro R P D D' hP hp t
    simpa using (hT R).2 D' P D P (Or.inr hP) (Or.inr hP) t (𝟙 P)

attribute [local irreducible] representatives

private theorem chain_square (E : Representatives.{c, v, r, w} (J := J) M) :
    ChainSquare.{c, v, r, w} (J := J) M μ E
      (chainPresentation.{c, v, r, w} (J := J) M μ) := by
  unfold ChainSquare
  intro R S R' S' φ a d φ' h
  obtain ⟨Q, hQ⟩ := (ordinaryData.{c, v, r, w} (J := J) M μ).coefficientSquares φ a d φ' h
  refine ⟨Q, hQ, ?_⟩
  let E' : ScalarOrdinaryEvaluation.Evaluation.{c, v, r} (J := J) (ordinaryScalars.{c, v, r, w} (J
    := J) M) :=
    { scalarEvaluate := E.scalarEvaluate, scalarEvaluate_pure := E.scalarEvaluate_pure }
  exact ScalarOrdinaryEvaluation.coefficient_square.{c, v, r} (J := J) (ordinaryScalars.{c, v, r,
    w} (J := J) M) (ordinaryTensor.{c, v, r, w} (J := J) M μ)
    E' (ordinaryData.{c, v, r, w} (J := J) M μ).presentation φ a d φ' Q hQ

set_option maxHeartbeats 800000 in
-- Four adjunction bijections and functorial tensor maps are compared explicitly.
private theorem restricted_uncurry {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (X K L : DerivedCategory (scalarModules J R))
    (β : X ⟶ (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) :
    (((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R).transpose _ K
        ((scalarDerivedRestriction a).obj (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M)
          a).derived.obj L))).symm
      ((scalarDerivedRestriction a).map (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M)
        a).derived.map β) ≫
        (scalarDerivedRestriction a).map
          (coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
            ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S) ((ScalarHomModels.scalar.{c, v,
            r, w} (J := J) M) a).derived
            (μ a).iso K L) ≫
        (Θ.iso a).hom.app (op K, ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.obj
          L)) =
      unitTensor.{c, v, r, w} (J := J) M μ a (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M)
        a).derived.obj X) K ≫
        (scalarDerivedRestriction a).map ((μ a).iso.inv.app (X, K)) ≫
        (scalarDerivedRestriction a).map (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M)
          a).derived.map
          ((((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R).transpose X K L).symm β)) := by
  have hr := Θ.representing a
    ((scalarDerivedRestriction a).obj (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M)
      a).derived.obj X)) K
    (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.obj L)
    ((scalarDerivedRestriction a).map (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M)
      a).derived.map β) ≫
      (scalarDerivedRestriction a).map
        (coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
          ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S) ((ScalarHomModels.scalar.{c, v, r,
          w} (J := J) M) a).derived
          (μ a).iso K L))
  rw [← Category.assoc, ← hr]
  convert scalar_bijection_baseChange ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
    ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S)
    ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).adjunction (μ a).iso X K L β using 1 <;>
    simp only [unitTensor, scalarHomBijection, scalarHomRestrictionTensor,
      ClosedScalarHom.bijection, ClosedScalarHom.restrictionTensor,
      CoefficientClosedStructure.tensor, Category.assoc]
  all_goals rfl

private theorem exactRepresentative_naturality
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (q : ∀ D : StrictScalarHom.Complex.{c, v, r} R, IsIso (representative.{c, v, r, w} (J := J) M
      a D))
    {D I : StrictScalarHom.Complex.{c, v, r} R} (f : D ⟶ I) :
    (scalarDerivedRestriction a).map (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M)
      a).derived.map (DerivedCategory.Q.map f)) ≫
        (exactRepresentative.{c, v, r, w} (J := J) M a q I).hom =
      (exactRepresentative.{c, v, r, w} (J := J) M a q D).hom ≫ DerivedCategory.Q.map
        ((StrictScalarHom.restriction.{c, v, r} a).map ((extension.{c, v, r, w} (J := J) M a).map
          f)) := by
  have hn := (ScalarHomTensor.pairComparison (J := J) M a).naturality f
  rw [ScalarHomTensor.pairComparison_app, ScalarHomTensor.pairComparison_app] at hn
  have hU := congrArg (scalarDerivedRestriction a).map hn
  simp only [Functor.map_comp] at hU
  simp only [exactRepresentative, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  erw [← Category.assoc, hU]
  erw [Category.assoc, (scalarRestrictionComparison a).hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rfl

set_option maxHeartbeats 800000 in
-- The representative expression contains the two normalized scalar comparison maps.
private theorem derived_evaluation (E : Representatives.{c, v, r, w} (J := J) M)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (ha : PreservesFiniteLimits ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).extension)
    (P I D : StrictScalarHom.Complex.{c, v, r} R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hp : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (_hI : I.IsKInjective) (b : D ⟶ homComplex (R := R) P I) :
    extendedEvaluation.{c, v, r, w} (J := J) M μ a (E.exact_computes a ha) (E.nu a) D P I
      (E.tensorIso P hP hp D) (E.tensorIso P hP hp ((StrictScalarHom.tensor.{c, v, r} a).obj D))
      (E.evaluate P I D b) = DerivedCategory.Q.map (E.scalarEvaluate a P I D b) := by
  let T := coefficientTotalTensor.{r, c, v} J R
  let k : T.obj ((StrictScalarHom.tensor.{c, v, r} a).obj D, P) ⟶
      (StrictScalarHom.restriction.{c, v, r} a).obj
        ((extension.{c, v, r, w} (J := J) M a).obj (T.obj (D, P))) :=
    T.map (Prod.mkHom ((E.nu a).hom.app D) (𝟙 P)) ≫
      E.chainUnitTensor a D P ≫
      (StrictScalarHom.restriction.{c, v, r} a).map ((μ a).complexIso D P).inv
  have hk : ∀ (n j l : ℤ) (h : n + j = l) (V : Cᵒᵖ)
      (s : S.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X j).val.obj V),
      (k.f l).val.app V (coefficientTensorGenerator.{r, c, v} J R _ P n j l h V
        (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p) =
      s • scalarHomUnitSection.{c, v, r, w} (J := J) M a ((T.obj (D, P)).X l) V
        (coefficientTensorGenerator.{r, c, v} J R D P n j l h V x p) := by
    intro n j l h V s x p
    change (((μ a).complexIso D P).inv.f l).val.app V
      (((E.chainUnitTensor a D P).f l).val.app V
        (((T.map (Prod.mkHom ((E.nu a).hom.app D) (𝟙 P))).f l).val.app V
          (coefficientTensorGenerator.{r, c, v} J R _ P n j l h V
            (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p))) = _
    erw [ScalarHomTensor.tensor_generator_map, E.nu_pure]
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply]
    erw [E.chainUnitTensor_pure, tensorComparison_inv_pure]
    rfl
  have hm := scalarTensorExactRepresentative.{c, v, r, w} (J := J) M μ a (E.exact_computes a ha)
    (E.nu a) (E.nu_pure a) P D hP (E.tensorIso P hP hp)
    (fun X hX ↦ E.tensorIso_normalization P X hP hp hX)
    (fun X Y t ↦ E.tensorIso_natural P Y X hP hp t) k hk
  change _ = DerivedCategory.Q.map k at hm
  have hf := exactRepresentative_naturality.{c, v, r, w} (J := J) M a (E.exact_computes a ha)
    (E.evaluate P I D b)
  unfold extendedEvaluation
  simp only [Functor.map_comp, Category.assoc]
  rw [hf]
  have hc : k ≫ (StrictScalarHom.restriction.{c, v, r} a).map
      ((extension.{c, v, r, w} (J := J) M a).map (E.evaluate P I D b)) = E.scalarEvaluate a P I D
        b :=
    scalar_chain_formula.{c, v, r, w} (J := J) M μ E a P I D b
  rw [← hc, DerivedCategory.Q.map_comp, ← hm]
  simp only [sourceTransport, unitTensor, exactRepresentative, Category.assoc]

set_option maxHeartbeats 800000 in
-- The calculation compares the normalized adjunction with the same chain evaluation.
private theorem calculation (E : Representatives.{c, v, r, w} (J := J) M) : Calculation.{c, v, r,
  w} (J := J) M μ Θ E := by
  refine ⟨derived_evaluation.{c, v, r, w} (J := J) M μ E, ?_, ?_⟩
  · intro R S a ha P I D hP hp hI b
    rw [← derived_evaluation.{c, v, r, w} (J := J) M μ E a ha P I D hP hp hI b]
    unfold adjunctionEvaluation extendedEvaluation
    rw [restricted_uncurry]
    simp only [transpose, Equiv.symm_apply_apply, Category.assoc]
  · intro R S a ha P I D V hP hp hI b t hV hv ht
    have hh := ScalarOrdinaryEvaluation.resolution.{c, v, r} (J := J)
      (ordinaryScalars.{c, v, r, w} (J := J) M)
        (ordinaryRepresentative.{c, v, r, w} (J := J) M E) a ha P I D V hP b t ht
    refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, ?_⟩
    rw [scalar_chain_formula.{c, v, r, w} (J := J) M μ E a P I V (t ≫ b)]
    exact hh.2.2.2.2

/-- Flat scalar evaluation, arbitrary-first-complex descent, normalized scalar-Hom
transposition and coherence for all derived inputs and coefficient squares.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 08J9, 06YP and 0D6D;
the agent refinement recorded in the node, not a verbatim theorem of these tags
(blueprint: lem-sfb-hom-flat-scalar-evaluation-model).

Proof:
1. Exact extension preserves cohomology and quasi-isomorphisms
   (lem-weil-pbc-exact-functor-complex-cohomology). Its universal factorization
   is both derived functors (lem-weil-pbc-exact-functor-derived-factorization,
   lem-weil-pbc-exact-functor-derived-functor). Uniqueness, together with
   lem-pur-derived-change-of-rings, identifies the given counit on every complex.
   Restriction leaves the abelian sheaf complex unchanged and is exact.
2. The one-factor tensor theorem (lem-sfb-hom-kflat-chain-transpose) applies
   to D,P and also to S tensor D,P. Its tensor comparison is natural and agrees
   with the fixed model on K-flat first factors. Evaluate the actual Hom product
   projections (def-coef-hom-representative-evaluation). The strict scalar
   identification (lem-sfb-hom-scalar-chain-identification) gives the chain map
   h_b((s tensor x) tensor p) = s tensor b(x)(p).
3. For K-flat V, resolve UEV by a flat-term K-flat W (lem-pc-kflat-resolution).
   The normalized scalar adjunction (lem-pur-sheaf-ring-derived-coefficient-adjunction)
   and scalar tensor square identify the unit map on W,P with z tensor p mapped
   to w(z) tensor (1 tensor p). The one-factor theorem cancels w tensor 1_P;
   no K-flatness of UEV is used.
4. Resolve D by any flat-term K-flat V. On V,P, the prescribed tensor square
   sends 1 tensor (v tensor p) to (1 tensor v) tensor (1 tensor p).
   Its inverse after unit insertion sends (s tensor v) tensor p to
   s tensor (v tensor p), so extended evaluation has the displayed h_b formula.
5. Tensoring t with P preserves quasi-isomorphisms
   (lem-pur-kflat-tensor-quasiiso-independent); exact extension preserves Et
   and E(t tensor 1). The same applies to UEt tensor 1. Both chain routes in
   resolution send (s tensor v) tensor p to s tensor b(t(v))(p).
   Localize and cancel this invertible precomposition. Every resolution gives
   the same actual h_b, including D = Hom(P,I), with no K-flatness of D or A.
6. The evaluation normalization of lem-sfb-dc-hom-scalar-adjunction identifies
   the transpose of Theta U(c) UF(beta) with UF(evaluation) U(mu inverse)
   followed by the scalar-unit tensor map. Naturality moves beta inside UF.
   Steps 2--5 identify this with Q(h_b), in the specified representatives.
7. Uncurry both naturality routes for any derived f,g. Naturality of mu and
   evaluation gives the same map F(g evaluation (1 tensor f)). Injectivity
   of the closed transpose proves naturality.
8. This applies to inverse localized quasi-isomorphisms as actual derived
   morphisms; functors carry those inverses to inverses. No chain-map-only
   presentation of derived morphisms is assumed.
9. Uncurry the successive comparisons for a,b. The result is GF(evaluation)
   G(mu_a inverse) mu_b inverse. Tensor coherence
   (lem-sfb-scalar-hom-tensor-coherence) identifies this with the transpose
   for ab, with the canonical source and both Hom-input transports.
10. The identity part of tensor coherence makes its transpose evaluation,
    hence its Hom comparison identity. Apply the composition result to the
    two paths of every commuting coefficient square to obtain derived_square.
11. Before localization, the normalized strict coefficient maps
    (lem-sfb-scalar-hom-chain-coefficient-coherence and
    lem-sfb-hom-scalar-chain-identification) give chain_square: both sides
    send r' tensor ((s tensor x) tensor p) to phi'(r') d(s) tensor
    (1 tensor b(x)(p)). Their actual Hom-product projections agree.
    Tensor generation and sheafification prove the chain equality. The same
    formulas give scalar multiplication for identity coefficients and
    t tensor (s tensor z) mapped to t b(s) tensor z for towers.
    Steps 5 and 9--10 descend those same identities. All complexes may be
    unbounded, coefficient rings may be zero, and no finiteness or continuity
    hypothesis has been used. -/
theorem model_exists : Nonempty (Model.{c, v, r, w} (J := J) M μ Θ) := by
  classical
  let E := representatives.{c, v, r, w} (J := J) M μ
  exact ⟨⟨E, calculation.{c, v, r, w} (J := J) M μ Θ E, chainPresentation.{c, v, r, w} (J := J) M
    μ, chain_square.{c, v, r, w} (J := J) M μ E,
    derived_coherence.{c, v, r, w} (J := J) M μ⟩⟩

end CategoryTheory.FlatScalarEvaluation
