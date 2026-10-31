/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ScalarInternalHomDataSupplement
public import WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
import WeilConjectures.Algebra.Homology.KFlatTelescopeClosure
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
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Etale derived scalar extension as tensor with the restricted coefficient

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 07A4, 07A6, 06YU and 0D6D;
sites-modules.tex, Tag 03EK; current blueprint, the constant-tensor paragraph of
lem-pur-ordinary-kunneth-finite-ring (blueprint: lem-pur-etale-scalar-tensor-identification).

## Main definitions

* `Identification`: the normalized natural comparison and all its compatibility equations.
* `tensorDerived`: specialization of the existing unbounded derived tensor functor.
* `ExactCompatible`: signed shift and distinguished cone triangle compatibility.

## Main statements

* `etaleScalarTensorIdentification`: existence on the small etale site of any scheme.

The auxiliary definitions only name the existing functors and the normalization equations.
A scalar pair is the recorded universal derived pair with its normalized adjunction.
The comparison is normalized before localization, including its signed shift and cone
triangles. Coefficient composition is an equality of derived arrows, with both intervening
comparison isomorphisms fixed by their balanced chain formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r w u
open CategoryTheory CategoryTheory.Limits SheafOfModules
open scoped ChangeOfRings

namespace SheafOfModules.EtaleScalarTensor

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The actual regular module of the coefficient ring sheaf.
Source: Stacks 03EK (blueprint: lem-pur-etale-scalar-tensor-identification). -/
abbrev regular (R : Sheaf J CommRingCat.{max c v r}) : scalarModules J R :=
  SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- The new coefficient ring with the old scalar action.
Source: Stacks 03EK (blueprint: lem-pur-etale-scalar-tensor-identification). -/
abbrev coefficient {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) :=
  (scalarRestriction φ).obj (regular.{c, v, r} S)

/-- The ordinary signed total tensor with the restricted coefficient in degree zero.
Source: Stacks 06YU (blueprint: lem-pur-etale-scalar-tensor-identification). -/
abbrev tensorComplex {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) :=
  (SiteTensorComplexFunctor R).flip.obj (siteTensorSingle (coefficient.{c, v, r} φ))

variable [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- The published unbounded derived tensor, specialized in the second argument.
Source: Stacks 06YU (blueprint: lem-pur-etale-scalar-tensor-identification). -/
abbrev tensorDerived {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) :=
  (siteRestrictionDerivedTensor (R := R)).flip.obj
    (DerivedCategory.Q.obj (siteTensorSingle (coefficient.{c, v, r} φ)))

/-- Restriction of the universal scalar counit, followed by exact restriction's comparison.
Source: Stacks 06YY, 07A6 (blueprint: lem-pur-etale-scalar-tensor-identification). -/
def restrictedComparison {R S : Sheaf J CommRingCat.{max c v r}} {φ : R ⟶ S}
    (s : ScalarDerivedPair φ) (P : CochainComplex (scalarModules J R) ℤ) :=
  (scalarDerivedRestriction φ).map
      (scalarPairComplexComparison s.extension s.extension_additive s.derived s.counit P) ≫
    (scalarRestrictionComparison φ).hom.app
      ((scalarComplex s.extension s.extension_additive).obj P)

/-- The coefficient compositor fixed by the normalized scalar adjunctions.
Source: Stacks 0D6D, 07A6 (blueprint: lem-pur-etale-scalar-tensor-identification). -/
def extensionComposition
    (s : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S), ScalarDerivedPair φ)
    {R S T : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) (ψ : S ⟶ T) :
    (s φ).derived ⋙ (s ψ).derived ≅ (s (φ ≫ ψ)).derived :=
  Adjunction.leftAdjointUniq ((s φ).adjunction.comp (s ψ).adjunction)
    ((s (φ ≫ ψ)).adjunction.ofNatIsoRight (scalarHomRestrictionComp.{c, v, r, w} φ ψ))

/-- The specified restricted coefficient compositor, oriented as in the DAG square.
Source: Stacks 0D6D (blueprint: lem-pur-etale-scalar-tensor-identification). -/
def gamma
    (s : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S), ScalarDerivedPair φ)
    {R S T : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) (ψ : S ⟶ T)
    (K : DerivedCategory (scalarModules J R)) :
    (scalarDerivedRestriction (φ ≫ ψ)).obj ((s (φ ≫ ψ)).derived.obj K) ≅
      (scalarDerivedRestriction φ).obj
        ((scalarDerivedRestriction ψ).obj ((s ψ).derived.obj ((s φ).derived.obj K))) :=
  (scalarHomRestrictionComp.{c, v, r, w} φ ψ).app ((s (φ ≫ ψ)).derived.obj K) ≪≫
    (scalarDerivedRestriction φ).mapIso
      ((scalarDerivedRestriction ψ).mapIso
        ((extensionComposition.{c, v, r, w} s φ ψ).symm.app K))

/-- Standard signed shifts on the termwise scalar functor.
Source: Stacks 06YU (blueprint: lem-pur-etale-scalar-tensor-identification). -/
@[instance_reducible] def complexShift {R S : Sheaf J CommRingCat.{max c v r}} {φ : R ⟶ S}
    (s : ScalarDerivedPair φ) :
    (scalarComplex s.extension s.extension_additive).CommShift ℤ :=
  letI := s.extension_additive
  inferInstanceAs ((s.extension.mapHomologicalComplex (.up ℤ)).CommShift ℤ)

/-- Standard signed shifts on the homotopy scalar functor.
Source: Stacks 06YY (blueprint: lem-pur-etale-scalar-tensor-identification). -/
@[instance_reducible] def homotopyShift {R S : Sheaf J CommRingCat.{max c v r}} {φ : R ⟶ S}
    (s : ScalarDerivedPair φ) :
    (scalarHomotopy s.extension s.extension_additive).CommShift ℤ :=
  letI := s.extension_additive
  inferInstanceAs ((s.extension.mapHomotopyCategory (.up ℤ)).CommShift ℤ)

/-- Canonical shifts on exact derived restriction.
Source: Stacks 07A6 (blueprint: lem-pur-etale-scalar-tensor-identification). -/
@[instance_reducible] def restrictionShift {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) :
    (scalarDerivedRestriction φ).CommShift ℤ :=
  inferInstanceAs ((scalarRestriction φ).mapDerivedCategory.CommShift ℤ)

/-- The existing signed shift in the first variable of the total tensor.
Source: Stacks 06YU (blueprint: lem-pur-etale-scalar-tensor-identification). -/
@[instance_reducible] def tensorShift
    {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) :
    (tensorComplex.{c, v, r} φ).CommShift ℤ :=
  letI := SheafOfModules.monoidalCategory R
  inferInstanceAs
    (((MonoidalCategory.curriedTensor (scalarModules J R)).map₂CochainComplex.flip.obj
      (siteTensorSingle (coefficient.{c, v, r} φ))).CommShift ℤ)

/-- The actual ordinary coefficient unit on cochain complexes.
Source: Stacks 03EK, 07A6 (blueprint: lem-pur-etale-scalar-tensor-identification). -/
def chainUnit {R S : Sheaf J CommRingCat.{max c v r}} {φ : R ⟶ S}
    (s : ScalarDerivedPair φ) (P : CochainComplex (scalarModules J R) ℤ) :
    P ⟶ ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj
      ((scalarComplex s.extension s.extension_additive).obj P) :=
  letI := s.extension_additive
  (s.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P

/-- Exactness compatibility relative to the canonical signed scalar counit.
The counit equation fixes the scalar shift; the normalized comparison then fixes the
fixed-coefficient tensor shift. `NatTrans.CommShift` makes the three components a
morphism of mapped cone triangles, including their signed third arrow.
Source: Stacks 06YU, 06YY (blueprint: lem-pur-etale-scalar-tensor-identification). -/
def ExactCompatible {R S : Sheaf J CommRingCat.{max c v r}} {φ : R ⟶ S}
    (s : ScalarDerivedPair φ)
    (i : s.derived ⋙ scalarDerivedRestriction φ ≅ tensorDerived.{c, v, r, w} φ) : Prop :=
  letI := homotopyShift.{c, v, r, w} s
  letI := restrictionShift.{c, v, r, w} φ
  ∃ sd : s.derived.CommShift ℤ,
    letI := sd
    ∃ st : (tensorDerived.{c, v, r, w} φ).CommShift ℤ,
      letI := st
      NatTrans.CommShift s.counit ℤ ∧ s.derived.IsTriangulated ∧
        (tensorDerived.{c, v, r, w} φ).IsTriangulated ∧ NatTrans.CommShift i.hom ℤ

/-- The normalized comparison for every coefficient map, and its adjunction and exactness
compatibilities. The chain isomorphism is specified on local tensor generators, not by
an arbitrary isomorphism of the derived objects. The same one-sided comparisons occur
in every equation. Source: Stacks 03EK, 06YU, 06YY, 07A6 and 0D6D
(blueprint: lem-pur-etale-scalar-tensor-identification). -/
structure Identification
    (s : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S), ScalarDerivedPair φ) where
  /-- The existing canonical one-sided tensor computations. -/
  computation : ∀ R : Sheaf J CommRingCat.{max c v r}, OneSidedTensorComparison (R := R)
  /-- Their normalization by the published two-sided resolving computation. -/
  computation_canonical : ∀ R, CanonicalOneSidedTensorComparison (computation R)
  /-- The tensor identity on complexes, natural in the complex. -/
  chain : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S),
    scalarComplex (s φ).extension (s φ).extension_additive ⋙
        (scalarRestriction φ).mapHomologicalComplex (.up ℤ) ≅ tensorComplex.{c, v, r} φ
  /-- The ordinary scalar-first convention is swapped to x tensor b. -/
  chain_pure : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (V : Cᵒᵖ)
    (x : (P.X n).val.obj V) (b : S.obj.obj V),
    HEq ((((chain φ).hom.app P).f n).val.app V
        (siteExtensionTmul φ (P.X n) (s φ).extension (s φ).extension_obj V x b))
      (siteTotalTmul P (siteTensorSingle (coefficient.{c, v, r} φ)) n 0 V x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (coefficient.{c, v, r} φ)).inv.val.app V b))
  /-- The natural isomorphism on the entire unbounded derived category. -/
  iso : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S),
    (s φ).derived ⋙ scalarDerivedRestriction φ ≅ tensorDerived.{c, v, r, w} φ
  /-- The pure-tensor identity through the specified scalar and tensor computations. -/
  normalization : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (P : CochainComplex (scalarModules J R) ℤ) (hP : TensorFlatRepresentative P),
    (iso φ).hom.app (DerivedCategory.Q.obj P) ≫
        (computation R P hP (siteTensorSingle (coefficient.{c, v, r} φ))).hom =
      restrictedComparison.{c, v, r, w} (s φ) P ≫ DerivedCategory.Q.map ((chain φ).hom.app P)
  /-- The unit becomes x mapped to x tensor 1 on a resolving complex. -/
  unit : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (P : CochainComplex (scalarModules J R) ℤ) (hP : TensorFlatRepresentative P),
    (s φ).adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (iso φ).hom.app (DerivedCategory.Q.obj P) ≫
        (computation R P hP (siteTensorSingle (coefficient.{c, v, r} φ))).hom =
      DerivedCategory.Q.map
        (chainUnit.{c, v, r, w} (s φ) P ≫
          (chain φ).hom.app P)
  /-- The counit becomes the actual tensor action b times g(x). This equation is
  cleared of the inverse resolution; for a quasi-isomorphism g it is the counit formula. -/
  counit : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (P : CochainComplex (scalarModules J R) ℤ) (hP : TensorFlatRepresentative P)
    (H : CochainComplex (scalarModules J S) ℤ)
    (g : P ⟶ ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj H),
    (scalarDerivedRestriction φ).map
        ((s φ).derived.map (DerivedCategory.Q.map g ≫
            (scalarRestrictionComparison φ).inv.app H) ≫
          (s φ).adjunction.counit.app (DerivedCategory.Q.obj H)) ≫
        (scalarRestrictionComparison φ).hom.app H =
      (iso φ).hom.app (DerivedCategory.Q.obj P) ≫
        (computation R P hP (siteTensorSingle (coefficient.{c, v, r} φ))).hom ≫
        DerivedCategory.Q.map ((chain φ).inv.app P ≫
          ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).map
            (scalarChainTranspose φ (s φ).extension (s φ).extension_additive
              (s φ).ordinaryAdjunction P H g))

  /-- The chain identity respects the standard signed shifts. -/
  chain_shift : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S),
    letI := complexShift.{c, v, r, w} (s φ)
    letI := tensorShift.{c, v, r} φ
    NatTrans.CommShift (chain φ).hom ℤ
  /-- Consequently its descended comparison respects shifts and cone triangles. -/
  exact : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S),
    ExactCompatible.{c, v, r, w} (s φ) (iso φ)
  /-- The inverse balanced comparison used in coefficient composition. -/
  balanced : ∀ {R S T : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) (ψ : S ⟶ T),
    ((s φ).derived ⋙ tensorDerived.{c, v, r, w} ψ) ⋙ scalarDerivedRestriction φ ≅
      tensorDerived.{c, v, r, w} (φ ≫ ψ)
  /-- Its ordinary chain representative; the scalar on the middle factor is multiplied
  into the last factor. -/
  balancedChain : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (P : CochainComplex (scalarModules J R) ℤ),
    ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj
        ((tensorComplex.{c, v, r} ψ).obj
          ((scalarComplex (s φ).extension (s φ).extension_additive).obj P)) ≅
      (tensorComplex.{c, v, r} (φ ≫ ψ)).obj P
  /-- The prescribed balanced formula (x tensor b) tensor c maps to x tensor ψ(b)c. -/
  balanced_pure : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (P : CochainComplex (scalarModules J R) ℤ)
    (n : ℤ) (V : Cᵒᵖ) (x : (P.X n).val.obj V) (b : S.obj.obj V) (z : T.obj.obj V),
    ((balancedChain φ ψ P).hom.f (n + 0)).val.app V
        (siteTotalTmul
          ((scalarComplex (s φ).extension (s φ).extension_additive).obj P)
          (siteTensorSingle (coefficient.{c, v, r} ψ)) n 0 V
          (siteExtensionTmul φ (P.X n) (s φ).extension (s φ).extension_obj V x b)
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (coefficient.{c, v, r} ψ)).inv.val.app V z)) =
      siteTotalTmul P (siteTensorSingle (coefficient.{c, v, r} (φ ≫ ψ))) n 0 V x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (coefficient.{c, v, r} (φ ≫ ψ))).inv.val.app V
          ((ψ.hom.app V).hom b * z))
  /-- The balanced derived comparison is the class of that precise chain map. -/
  balanced_normalization : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (P : CochainComplex (scalarModules J R) ℤ)
    (hP : TensorFlatRepresentative P)
    (hEP : TensorFlatRepresentative
      ((scalarComplex (s φ).extension (s φ).extension_additive).obj P)),
    (balanced φ ψ).hom.app (DerivedCategory.Q.obj P) ≫
        (computation R P hP (siteTensorSingle (coefficient.{c, v, r} (φ ≫ ψ)))).hom =
      (scalarDerivedRestriction φ).map
        (((siteRestrictionDerivedTensor (R := S)).map
            (scalarPairComplexComparison (s φ).extension (s φ).extension_additive
              (s φ).derived (s φ).counit P)).app
            (DerivedCategory.Q.obj (siteTensorSingle (coefficient.{c, v, r} ψ))) ≫
          (computation S
            ((scalarComplex (s φ).extension (s φ).extension_additive).obj P) hEP
            (siteTensorSingle (coefficient.{c, v, r} ψ))).hom) ≫
        (scalarRestrictionComparison φ).hom.app
          ((tensorComplex.{c, v, r} ψ).obj
            ((scalarComplex (s φ).extension (s φ).extension_additive).obj P)) ≫
        DerivedCategory.Q.map (balancedChain φ ψ P).hom
  /-- The actual coefficient-composition square in the derived category. -/
  composition : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (K : DerivedCategory (scalarModules J R)),
    (gamma.{c, v, r, w} s φ ψ K).hom ≫
        (scalarDerivedRestriction φ).map ((iso ψ).hom.app ((s φ).derived.obj K)) ≫
        (balanced φ ψ).hom.app K = (iso (φ ≫ ψ)).hom.app K

/-- The standard small model in any coefficient universe containing the site's objects.
Both object and Hom smallness are supplied explicitly; no equality of sizes is imposed.
Source: Stacks 03EK (blueprint: lem-pur-etale-scalar-tensor-identification). -/
instance etaleSmall (X : AlgebraicGeometry.Scheme.{u}) [UnivLE.{u + 1, r}] :
    EssentiallySmall.{r} X.Etale :=
  letI : UnivLE.{u, r} := @UnivLE.trans.{u, u + 1, r} inferInstance inferInstance
  essentiallySmall_of_small_of_locallySmall X.Etale

/-- Sheafification at the actual independent coefficient size on the etale site.
This is the existing small-model sheafification; the size argument is explicit so
instance search need not solve an equation expressing a maximum as a successor.
Source: Stacks 03EK (blueprint: lem-pur-etale-scalar-tensor-identification). -/
instance (priority := high) etaleSheafify (X : AlgebraicGeometry.Scheme.{u})
    [UnivLE.{u + 1, r}] : HasSheafify X.smallEtaleTopology AddCommGrpCat.{r} :=
  hasSheafifyEssentiallySmallSite.{u, r, u + 1, r + 1, r}
    X.smallEtaleTopology AddCommGrpCat.{r}

/-- The standard local-bijection description at that same coefficient size.
Source: Stacks 03EK (blueprint: lem-pur-etale-scalar-tensor-identification). -/
instance (priority := high) etaleLocalBijections (X : AlgebraicGeometry.Scheme.{u})
    [UnivLE.{u + 1, r}] :
    X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, r, u + 1,
    r + 1, r, r, r} X.smallEtaleTopology

/-- Exact restriction of derived coefficient extension is the published derived tensor
with the restricted coefficient ring, with all the normalizations and compatibilities
of `Identification`. The scheme is arbitrary. Coefficient, site, and localization sizes
are not equated. The family `s` consists of presentations of the existing universal
scalar-derived pairs, not additional flatness or finiteness assumptions.

Source: Stacks Project, Tags 06YY, 07A4, 07A6, 06YU and 0D6D; Modules on Sites, 03EK;
current blueprint, constant-tensor paragraph of lem-pur-ordinary-kunneth-finite-ring
(blueprint: lem-pur-etale-scalar-tensor-identification).

Proof:
1. Resolve an arbitrary complex by a flat-term K-flat complex P. Derived change of
rings computes extension by P tensor S. Exact restriction is termwise restriction;
its localization comparison gives `restrictedComparison`.
2. The ordinary right unitor sends m tensor b to bm; its inverse sends m to m tensor 1.
Balancing proves that these are inverse maps, natural and compatible with restriction.
They sheafify and give inverse chain maps. The regular S-module is flat, and S[0] is
flat-term K-flat. Two-sided tensor descent therefore localizes these chain unitors to
the right unitor on every unbounded S-derived object.
3. Specialize the balanced tensor/restriction isomorphism to the regular S-module and
follow by that unitor. Its inverse is `iso`. On P it sends b tensor x to x tensor b,
which gives `chain_pure` and `normalization`. Canonical one-sided computations are
normalized by the two-sided computations; localization gives naturality and independence
of the representative, including when the restricted S-module is not flat.
4. The normalized scalar unit is x mapped to 1 tensor x. Its composite with `chain` is
x mapped to x tensor 1, proving `unit`. The ordinary transpose of g is b tensor x mapped
to b g(x). The normalized derived transpose gives `counit`. For a quasi-isomorphism g,
invert its derived image to obtain the counit formula; P resolves the restricted complex,
so no preservation of K-flatness by restriction is used.
5. The degreewise tensor identity commutes with signed shifts and with the cone matrix
(d, f; 0, -d), on both summands. This gives `chain_shift`. Resolving localization descends
the scalar counit and the tensor shifts, and equality detection descends the same square
for `iso`. This gives `ExactCompatible`, hence compatibility on the three arrows of the
mapped cone triangle, including the signed connecting arrow.
6. For R to S to T, extension preserves flat-term K-flat complexes, so the same P computes
successive extension. The normalized adjoint compositor sends x tensor z to
(x tensor 1) tensor z. The inverse balanced comparison sends (x tensor b) tensor z to
x tensor ψ(b)z. These inverse chain maps are natural and balanced. Localization gives
`balanced`, with the displayed representative normalization. Both sides of `composition`
send x tensor z to x tensor z; equality detection on resolving complexes gives the
stated derived square. Associativity of multiplication also covers iterated composition;
identity coefficient maps reduce to the right unitor. No boundedness, perfectness or
flatness of a coefficient homomorphism occurs in any step. -/
theorem etaleScalarTensorIdentification (X : AlgebraicGeometry.Scheme.{u})
    [∀ R : Sheaf X.smallEtaleTopology CommRingCat.{max (u + 1) r},
      HasDerivedCategory.{w} (scalarModules X.smallEtaleTopology R)]
    (s : ∀ {R S : Sheaf X.smallEtaleTopology CommRingCat.{max (u + 1) r}}
      (φ : R ⟶ S), ScalarDerivedPair φ) :
    Nonempty (Identification.{u + 1, u, r, w} (J := X.smallEtaleTopology) s) := by
  sorry

end SheafOfModules.EtaleScalarTensor
