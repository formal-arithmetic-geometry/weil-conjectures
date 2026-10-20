/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
/-! # Internal Hom and arbitrary changes of ring-sheaf coefficients

Source: Bhatt--Scholze, Remark 6.8.15 (ambient derived operations);
Stacks Project, sites-cohomology.tex, Tags 07A6, 07A4, 08J9, 08JA and 0D6D,
and derived.tex, Tag 05RT
(blueprint: lem-sfb-dc-hom-scalar-adjunction).
This is the auxiliary scalar-adjunction comparison extracted from the final
paragraph of lem-sfb-dc-hom-preserves in the current blueprint.
Every comparison is normalized on actual K-flat tensors. In particular these
are ordinary unbounded module derived categories, with no flatness or
perfectness assumption on a coefficient map or a derived input.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open SheafOfModules
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- The recorded module category, with its ring-sheaf commutativity forgotten.
Source: Stacks 03DA (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
abbrev scalarModules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

variable {J} {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)

/-- Actual ordinary restriction along the given map of commutative ring sheaves.
Source: Stacks 03DA (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable abbrev scalarRestriction : scalarModules J S ⥤ scalarModules J R :=
  restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).map a)

variable [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)]

/-- Exact scalar restriction preserves finite limits, by the recorded adjunction theorem.
Source: Stacks 03DA and 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable instance scalarRestriction_limits :
    PreservesFiniteLimits (scalarRestriction a) :=
  (sheafRingDerivedCoefficientAdjunction a).choose

/-- Exact scalar restriction preserves finite colimits, by the recorded adjunction theorem.
Source: Stacks 03DA and 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable instance scalarRestriction_colimits :
    PreservesFiniteColimits (scalarRestriction a) :=
  (sheafRingDerivedCoefficientAdjunction a).choose_spec.choose

/-- Actual termwise application of an additive functor.
Source: Stacks 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarComplex (E : scalarModules J R ⥤ scalarModules J S)
    (hE : E.Additive) :
    CochainComplex (scalarModules J R) ℤ ⥤ CochainComplex (scalarModules J S) ℤ :=
  letI := hE
  E.mapHomologicalComplex (.up ℤ)

/-- Actual homotopy application of an additive functor.
Source: Stacks 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomotopy (E : scalarModules J R ⥤ scalarModules J S)
    (hE : E.Additive) :
    HomotopyCategory (scalarModules J R) (.up ℤ) ⥤
      HomotopyCategory (scalarModules J S) (.up ℤ) :=
  letI := hE
  E.mapHomotopyCategory (.up ℤ)

/-- Derived restriction is localization of the exact termwise restriction functor.
Source: Stacks 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarDerivedRestriction :
    DerivedCategory (scalarModules J S) ⥤ DerivedCategory (scalarModules J R) :=
  (scalarRestriction a).mapHomologicalComplexUpToQuasiIso (.up ℤ)

/-- The canonical termwise restriction comparison.
Source: Stacks 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarRestrictionComparison :
    DerivedCategory.Q ⋙ scalarDerivedRestriction a ≅
      (scalarRestriction a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (scalarRestriction a).mapHomologicalComplexUpToQuasiIsoFactors (.up ℤ)

/-- The representative comparison determined by a left-derived pair.
Source: Stacks 06YY (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarPairComplexComparison
    (E : scalarModules J R ⥤ scalarModules J S) (hE : E.Additive)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶ scalarHomotopy E hE ⋙ DerivedCategory.Qh)
    (P : CochainComplex (scalarModules J R) ℤ) :
    F.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj ((scalarComplex E hE).obj P) :=
  F.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _

/-- The actual chain transpose induced by an ordinary scalar adjunction.
Source: Stacks 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarChainTranspose
    (E : scalarModules J R ⥤ scalarModules J S) (hE : E.Additive)
    (am : E ⊣ scalarRestriction a)
    (P : CochainComplex (scalarModules J R) ℤ)
    (H : CochainComplex (scalarModules J S) ℤ)
    (g : P ⟶ ((scalarRestriction a).mapHomologicalComplex (.up ℤ)).obj H) :
    (scalarComplex E hE).obj P ⟶ H :=
  letI := hE
  ((am.mapHomologicalComplex (.up ℤ)).homEquiv P H).symm g

/-- A presentation of the canonical scalar adjunction, retaining every normalization.
The functors are fixed by their object/map formulas and left-derived universal property;
the adjunction is fixed by the sheafified scalar-unit equation and chain-transpose equation.
Source: Stacks 07A6; derived.tex 0FND and 09T5
(blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
structure ScalarDerivedPair where
  /-- The ordinary scalar tensor functor. -/
  extension : scalarModules J R ⥤ scalarModules J S
  /-- Its objects are the recorded sheafified scalar tensor objects. -/
  extension_obj : ∀ M, extension.obj M = changeOfRings a M
  /-- Its maps are the recorded sheafified scalar tensor maps. -/
  extension_map : ∀ {M N : scalarModules J R} (f : M ⟶ N),
    extension.map f = eqToHom (extension_obj M) ≫ changeOfRingsHom a M f ≫
      eqToHom (extension_obj N).symm
  /-- Scalar extension is additive. -/
  extension_additive : extension.Additive
  /-- The everywhere defined left derived extension. -/
  derived : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S)
  /-- Its defining universal comparison. -/
  counit : DerivedCategory.Qh ⋙ derived ⟶
    scalarHomotopy extension extension_additive ⋙ DerivedCategory.Qh
  /-- The recorded left-derived universal property. -/
  isLeftDerived : derived.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ))
  /-- Every K-flat complex computes this universal derived pair. -/
  computes : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      IsIso (scalarPairComplexComparison extension extension_additive derived counit P)
  /-- The ordinary scalar adjunction. -/
  ordinaryAdjunction : extension ⊣ scalarRestriction a
  /-- Its unit is sheafification of 1 tensor x, so no twisted adjunction is allowed. -/
  ordinaryUnit : ∀ (M : scalarModules J R) (V : Cᵒᵖ) (x : M.val.obj V),
    ((eqToHom (extension_obj M)).val.app V)
        ((ordinaryAdjunction.unit.app M).val.app V x) =
      (toSheafify J (changeOfRingsPresheaf a M).presheaf).app V
        ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app
          (M.val.obj V) x)
  /-- The unbounded derived extension/restriction adjunction. -/
  adjunction : derived ⊣ scalarDerivedRestriction a
  /-- The precise normalized derived transpose on K-flat representatives. -/
  normalization : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    ∀ (H : CochainComplex (scalarModules J S) ℤ)
      (g : P ⟶ ((scalarRestriction a).mapHomologicalComplex (.up ℤ)).obj H),
      (adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj H)).symm
          (DerivedCategory.Q.map g ≫ (scalarRestrictionComparison a).inv.app H) =
        scalarPairComplexComparison extension extension_additive derived counit P ≫
          DerivedCategory.Q.map (scalarChainTranspose a extension extension_additive
            ordinaryAdjunction P H g)

end SheafOfModules

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- A simultaneous presentation of the existing derived tensors and scalar adjunctions.
Each closed structure has the recorded representative evaluation normalization;
each scalar pair has actual sheafified tensor objects/maps and the universal
left-derived comparison, with its ordinary and derived unit normalizations.
Source: Stacks 06YY, 07A6, 08J9
(blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
structure ScalarHomModels where
  /-- The already recorded closed tensor-Hom structure for each coefficient sheaf. -/
  closed : ∀ R : Sheaf J CommRingCat.{max c v r},
    CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- Its fixed actual K-flat and Hom-complex representative normalization. -/
  model : ∀ R : Sheaf J CommRingCat.{max c v r},
    CoefficientTensorModels.{r, c, v, w} J R (closed R)
  /-- The normalized scalar adjunction for every actual ring-sheaf map. -/
  scalar : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), ScalarDerivedPair a

variable {J} (M : ScalarHomModels.{c, v, r, w} J)
  {R S T : Sheaf J CommRingCat.{max c v r}}

/-- Actual scalar-unit sections used by every tensor normalization below.
Source: Stacks 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomUnitSection (a : R ⟶ S) (P : scalarModules J R)
    (V : Cᵒᵖ) (x : P.val.obj V) : ((M.scalar a).extension.obj P).val.obj V :=
  ((M.scalar a).ordinaryAdjunction.unit.app P).val.app V x

/-- Strong scalar tensor comparison, retaining its actual pure-tensor normalization
before and after passage to the derived category.
Source: Stacks 07A4 and 0D6D
(blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
structure ScalarHomTensorComparison (a : R ⟶ S) where
  /-- Scalar extension carries K-flat complexes to K-flat complexes. -/
  preservesKFlat : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
  /-- The actual chain tensor comparison, with the differential signs retained. -/
  complexIso : ∀ (P Q : CochainComplex (scalarModules J R) ℤ),
    (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J S).obj
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P,
         (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)
  /-- It sends 1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). -/
  generators : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((complexIso P Q).hom.f k).val.app V
        (scalarHomUnitSection M a _ V
          (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
      coefficientTensorGenerator.{r, c, v} J S
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)
        p q k h V (scalarHomUnitSection M a _ V x) (scalarHomUnitSection M a _ V y)
  /-- The natural derived strong tensor comparison. -/
  iso : (M.closed R).tensor ⋙ (M.scalar a).derived ≅
    ((M.scalar a).derived.prod (M.scalar a).derived) ⋙ (M.closed S).tensor
  /-- Its defining square on the actual K-flat representatives. -/
  normalization : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
    (M.scalar a).derived.map
        ((CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
          P Q hp hq).hom) ≫
      iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (M.closed S).tensor.map (Prod.mkHom
          (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
            (M.scalar a).derived (M.scalar a).counit P)
          (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
            (M.scalar a).derived (M.scalar a).counit Q)) =
      scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
          (M.scalar a).derived (M.scalar a).counit
            ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (complexIso P Q).hom ≫
          (CoefficientTensorModels.iso.{r, c, v, w} J S (M.closed S) (M.model S)
            _ _ (preservesKFlat P hp) (preservesKFlat Q hq)).hom

/-- The actual source bifunctor U RHom_S(F(-),-).
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomSource (a : R ⟶ S) :
    (DerivedCategory (scalarModules J R))ᵒᵖ × DerivedCategory (scalarModules J S) ⥤
      DerivedCategory (scalarModules J R) :=
  ((M.scalar a).derived.op.prod (𝟭 _)) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J S ⋙ scalarDerivedRestriction a

/-- The actual target bifunctor RHom_R(-,U(-)).
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomTarget (a : R ⟶ S) :
    (DerivedCategory (scalarModules J R))ᵒᵖ × DerivedCategory (scalarModules J S) ⥤
      DerivedCategory (scalarModules J R) :=
  ((𝟭 _).prod (scalarDerivedRestriction a)) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J R

/-- The five canonical representing Hom bijections, in the order of the node's proof.
Source: Stacks 07A6, 07A4 and 08J9
(blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomBijection (a : R ⟶ S) (μ : ScalarHomTensorComparison M a)
    (A K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S)) :
    (A ⟶ (scalarHomSource M a).obj (op K, N)) ≃
      (A ⟶ (scalarHomTarget.{c, v, r, w} a).obj (op K, N)) :=
  Equiv.trans
    ((M.scalar a).adjunction.homEquiv A
      ((derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), N))).symm
    (Equiv.trans
      ((M.closed S).transpose ((M.scalar a).derived.obj A)
        ((M.scalar a).derived.obj K) N).symm
      (Equiv.trans (Iso.homCongr (μ.iso.app (A, K)).symm (Iso.refl N))
        (Equiv.trans ((M.scalar a).adjunction.homEquiv ((M.closed R).tensor.obj (A, K)) N)
          ((M.closed R).transpose A K ((scalarDerivedRestriction a).obj N)))))

/-- The canonical lax tensor map on scalar restriction, the counit mate of the
strong scalar extension tensor comparison.
Source: Stacks 07A4 and 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomRestrictionTensor (a : R ⟶ S) (μ : ScalarHomTensorComparison M a)
    (H V : DerivedCategory (scalarModules J S)) :
    (M.closed R).tensor.obj
        ((scalarDerivedRestriction a).obj H, (scalarDerivedRestriction a).obj V) ⟶
      (scalarDerivedRestriction a).obj ((M.closed S).tensor.obj (H, V)) :=
  (M.scalar a).adjunction.unit.app _ ≫
    (scalarDerivedRestriction a).map
      (μ.iso.hom.app _ ≫ (M.closed S).tensor.map
        (Prod.mkHom ((M.scalar a).adjunction.counit.app H)
          ((M.scalar a).adjunction.counit.app V)))

/-- Restricted S-linear evaluation after the actual scalar-extension unit.
Source: Stacks 07A6 and 08J9 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomRestrictedEvaluation (a : R ⟶ S) (μ : ScalarHomTensorComparison M a)
    (K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S)) :
    (M.closed R).tensor.obj ((scalarHomSource M a).obj (op K, N), K) ⟶
      (scalarDerivedRestriction a).obj N :=
  (M.closed R).tensor.map
      (Prod.mkHom (𝟙 _) ((M.scalar a).adjunction.unit.app K)) ≫
    scalarHomRestrictionTensor M a μ
      ((derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), N)) ((M.scalar a).derived.obj K) ≫
      (scalarDerivedRestriction a).map ((M.closed S).evaluation ((M.scalar a).derived.obj K) N)

/-- Termwise restriction composes by the identity on the underlying module sheaves.
Source: Stacks 0D6D and 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomOrdinaryRestrictionComp (a : R ⟶ S) (b : S ⟶ T) :
    scalarRestriction (a ≫ b) ≅ scalarRestriction b ⋙ scalarRestriction a :=
  Iso.refl _

/-- The canonical composition comparison for actual derived scalar restriction.
Source: Stacks 0D6D and 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomRestrictionComp (a : R ⟶ S) (b : S ⟶ T) :
    scalarDerivedRestriction (a ≫ b) ≅
      scalarDerivedRestriction b ⋙ scalarDerivedRestriction a :=
  Functor.mapDerivedCategoryNatIso (scalarHomOrdinaryRestrictionComp.{c, v, r} a b) ≪≫
    Functor.mapDerivedCategoryCompIso (scalarRestriction b) (scalarRestriction a)

/-- Identity coefficient restriction is the identity on the underlying module sheaves.
Source: Stacks 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomOrdinaryRestrictionId (R : Sheaf J CommRingCat.{max c v r}) :
    scalarRestriction (𝟙 R) ≅ 𝟭 (scalarModules J R) :=
  Iso.refl _

/-- The canonical identity comparison for actual derived scalar restriction.
Source: Stacks 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomRestrictionId (R : Sheaf J CommRingCat.{max c v r}) :
    scalarDerivedRestriction (𝟙 R) ≅ 𝟭 (DerivedCategory (scalarModules J R)) :=
  Functor.mapDerivedCategoryNatIso (scalarHomOrdinaryRestrictionId.{c, v, r} R) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The canonical scalar extension composition comparison, uniquely fixed by units.
On K-flat representatives it is t tensor (s tensor x) mapped to t b(s) tensor x;
this is the unique left-adjoint comparison for the actual restriction comparison.
Source: Stacks 0D6D and 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomExtensionComp (a : R ⟶ S) (b : S ⟶ T) :
    (M.scalar a).derived ⋙ (M.scalar b).derived ≅ (M.scalar (a ≫ b)).derived :=
  Adjunction.leftAdjointUniq ((M.scalar a).adjunction.comp (M.scalar b).adjunction)
    ((M.scalar (a ≫ b)).adjunction.ofNatIsoRight (scalarHomRestrictionComp.{c, v, r, w} a b))

/-- The unit-normalized identity comparison for scalar extension.
Source: Stacks 07A6 (blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
noncomputable def scalarHomExtensionId (R : Sheaf J CommRingCat.{max c v r}) :
    (M.scalar (𝟙 R)).derived ≅ 𝟭 (DerivedCategory (scalarModules J R)) :=
  Adjunction.leftAdjointUniq
    ((M.scalar (𝟙 R)).adjunction.ofNatIsoRight
      (scalarHomRestrictionId.{c, v, r, w} R)) Adjunction.id

/-- Every clause of the scalar internal-Hom comparison, with canonical maps fixed.
Naturality is encoded by the natural isomorphism of the two actual bifunctors.
Evaluation and representing Hom bijections uniquely determine it. The tower and
identity equations include all necessary coefficient transports explicitly.
Source: Stacks 07A6, 07A4, 08J9, 08JA, 0D6D and 05RT
(blueprint: lem-sfb-dc-hom-scalar-adjunction). -/
structure ScalarInternalHomAdjunction
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison M a) where
  /-- The comparison is natural contravariantly in K and covariantly in N. -/
  iso : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    scalarHomSource M a ≅ scalarHomTarget.{c, v, r, w} a
  /-- Its tensor-Hom transpose is restricted evaluation after the scalar unit. -/
  evaluation : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S)),
    ((M.closed R).transpose _ K ((scalarDerivedRestriction a).obj N)).symm
      ((iso a).hom.app (op K, N)) = scalarHomRestrictedEvaluation M a (μ a) K N
  /-- Evaluation normalization characterizes the isomorphism uniquely. -/
  unique : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (β : scalarHomSource M a ≅ scalarHomTarget.{c, v, r, w} a),
    (∀ (K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S)),
      ((M.closed R).transpose _ K ((scalarDerivedRestriction a).obj N)).symm
        (β.hom.app (op K, N)) = scalarHomRestrictedEvaluation M a (μ a) K N) → β = iso a
  /-- Equivalently, it induces the specified five representing Hom bijections. -/
  representing : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (A K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S))
    (t : A ⟶ (scalarHomSource M a).obj (op K, N)),
    scalarHomBijection M a (μ a) A K N t = t ≫ (iso a).hom.app (op K, N)
  /-- The direct and successive comparisons agree along every coefficient tower. -/
  composition : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (a : R ⟶ S) (b : S ⟶ T)
    (K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J T)),
    (iso (a ≫ b)).hom.app (op K, N) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K)) ((scalarHomRestrictionComp.{c, v, r, w} a b).hom.app N)) =
      (scalarHomRestrictionComp.{c, v, r, w} a b).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J T).obj
            (op ((M.scalar (a ≫ b)).derived.obj K), N)) ≫
        (scalarDerivedRestriction a).map ((scalarDerivedRestriction b).map
          ((derivedInternalHomOfUniverses.{c, v, r, w} J T).map
            (Prod.mkHom ((scalarHomExtensionComp M a b).hom.app K).op (𝟙 N)))) ≫
          (scalarDerivedRestriction a).map
            ((iso b).hom.app (op ((M.scalar a).derived.obj K), N)) ≫
              (iso a).hom.app (op K, (scalarDerivedRestriction b).obj N)
  /-- The identity coefficient comparison is the identity under the canonical transports. -/
  identity : ∀ (R : Sheaf J CommRingCat.{max c v r})
    (K N : DerivedCategory (scalarModules J R)),
    (iso (𝟙 R)).hom.app (op K, N) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K)) ((scalarHomRestrictionId.{c, v, r, w} R).hom.app N)) =
      (scalarHomRestrictionId.{c, v, r, w} R).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
            (op ((M.scalar (𝟙 R)).derived.obj K), N)) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom ((scalarHomExtensionId M R).inv.app K).op (𝟙 N))
  /-- Exact scalar restriction detects isomorphisms of all unbounded derived objects. -/
  conservative : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    {N N' : DerivedCategory (scalarModules J S)} (f : N ⟶ N'),
    IsIso ((scalarDerivedRestriction a).map f) → IsIso f

/-- The full unbounded scalar internal-Hom adjunction and all its normalizations.
The existential presentations are fixed by the recorded universal derived pairs,
actual pure-tensor formulas and representative evaluation. No arbitrary replacement
of tensor, internal Hom, restriction or the comparison map is admitted.
Source: Bhatt--Scholze, Remark 6.8.15, ambient derived operations;
Stacks Project, sites-cohomology.tex, Tags 07A6, 07A4, 08J9, 08JA and 0D6D;
derived.tex Tag 05RT
(blueprint: lem-sfb-dc-hom-scalar-adjunction).
Proof:
1. Use the normalized extension/restriction adjunction of
   lem-pur-sheaf-ring-derived-coefficient-adjunction. The identity geometric
   morphism with R to S in lem-weil-pbc-ringed-topoi-derived-tensor-pullback
   gives the strong tensor comparison. On actual tensors its formula is
   s tensor (x tensor y) mapped to (s tensor x) tensor (1 tensor y).
2. The internal-Hom identity of
   lem-weil-pbc-ringed-internal-hom-exact-restriction, followed by the global
   degree-zero comparison of lem-pur-rhom-global-sections, gives tensor-Hom
   transposition. Its evaluation is the fixed Hom-complex evaluation, as
   required by CoefficientTensorModels.uncurry_model.
3. Compose the five displayed Hom bijections: inverse scalar transpose,
   inverse S tensor-Hom transpose, precomposition with the strong tensor
   comparison, scalar transpose, and R tensor-Hom transpose. Each is natural.
4. On E = U H_S(F K,N), send 1_E through this chain to obtain alpha. Apply
   the inverse chain to 1_B, B = H_R(K,U N), to obtain its inverse. Naturality
   in the testing object proves both inverse identities and naturality in
   K,N. It also proves the representing equation and uniqueness.
5. Unwind the chain at 1_E. Move the scalar unit past the two tensor maps by
   naturality and use epsilon_(F K) F(eta_K) = 1. The transpose is precisely
   scalarHomRestrictedEvaluation, and transposition is bijective.
6. For R to S to T choose flat-term K-flat representatives (06YS).
   Both scalar extensions are computed by T tensor_S (S tensor_R P).
   The maps t tensor (s tensor x) to t b(s) tensor x and t tensor x to
   t tensor (1 tensor x) are inverse chain maps. Their unit normalization
   identifies this comparison with scalarHomExtensionComp. Restriction
   comparison is induced by the actual termwise identity on modules.
7. The two strong tensor maps send a pure tensor to
   (t b(s) tensor x) tensor (1 tensor y). Tensor descent
   (lem-weil-pbc-site-derived-tensor-descent) makes their derived maps equal.
   The composite scalar transpose is the transpose for the composite unit;
   hence the five Hom chains agree. This is the composition field. The
   same computation with the identity ring map proves the identity field.
8. Scalar restriction preserves kernels and cokernels and hence cohomology.
   It reflects isomorphisms of module sheaves: the inverse of an S-linear
   underlying sheaf isomorphism is S-linear. If U(f) is invertible, every
   restricted cohomology map is invertible, hence so is every cohomology
   map of f. Apply the unbounded criterion DerivedCategory.isIso_iff,
   lem-weil-pbc-unbounded-derived-iso-cohomology. -/
theorem scalarInternalHomAdjunction_exists :
    ∃ (M : ScalarHomModels.{c, v, r, w} J)
      (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
        ScalarHomTensorComparison M a), Nonempty (ScalarInternalHomAdjunction M μ) := by
  sorry

end CategoryTheory
