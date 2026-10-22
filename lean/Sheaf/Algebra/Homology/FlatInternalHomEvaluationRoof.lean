/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q01 and J2
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
import all Sheaf.Paper.DerivedInternalHomFilteredColimitData
import all Sheaf.Algebra.Homology.ScalarHomTensorCoherence
import all Sheaf.Algebra.Homology.ScalarHomTensorComparison
import all Sheaf.CategoryTheory.ClosedScalarHomComparison
import all Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.StrictHomNumeratorTranspose
import Sheaf.Algebra.Homology.FlatScalarEvaluationModel
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Flat scalar extension and the evaluation-normalized internal-Hom roof

Source: Stacks Project, sites-cohomology.tex, Tags 08J9 and 0A95; sites-modules.tex,
Tag 03CZ; the evaluation-roof refinement of the final paragraph of blueprint
main-20261015, lem-sfb-dc-hom-preserves.proof.md
(blueprint: lem-sfb-hom-flat-evaluation-roof).

The strict numerator and denominator are the recorded ones. The only representative
identifications introduced here are specified on actual sheafified tensor generators.
All derived comparisons are defined by transposing scalar-extended evaluation.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules WeilConjectures
open WeilConjectures.SfbHomFilteredColimit
open scoped ChangeOfRings

attribute [local irreducible] coefficientTotalTensor homComplexFunctor
  SheafOfModules.monoidalCategory scalarPairComplexComparison

attribute [local irreducible] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

namespace CategoryTheory.SfbFlatHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- The already recorded strict tensor functor with the restricted regular S-module.
This abbreviation uses restriction of scalars and the actual single-zero total tensor.
Source: Stacks 03CZ, 06YN (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def scalarTensor {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :
    CochainComplex (scalarModules J R) ℤ ⥤ CochainComplex (scalarModules J R) ℤ :=
  Prod.sectR ((scalarRestriction a).obj (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))
    (CochainComplex (scalarModules J R) ℤ) ⋙ tensor.{c, v, r} J R

variable (M : ScalarHomModels.{c, v, r, w} J)
  (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    ScalarHomTensorComparison M a)
  (α : ScalarInternalHomAdjunction M μ)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

/-- The fixed strict tensor comparison type, shared without changing its functors.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
abbrev ScalarTensorIdentification :=
  scalarTensor.{c, v, r} a ≅
    scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
      (scalarRestriction a).mapHomologicalComplex (.up ℤ)

/-- The family of the fixed strict tensor comparisons.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
abbrev ScalarTensorComparisons :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    ScalarTensorIdentification M a

/-- The canonical map c is the transpose of scalar-extended evaluation, with the
inverse strong tensor comparison in front of it. It is defined for all derived inputs.
Source: Stacks 08J9, 07A4 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def comparison (K L : DerivedCategory (scalarModules J R)) :
    (M.scalar a).derived.obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), (M.scalar a).derived.obj L) :=
  (M.closed S).transpose _ _ _
    ((μ a).iso.inv.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L), K) ≫
      (M.scalar a).derived.map ((M.closed R).evaluation K L))

/-- The precise map Theta U(c), using the recorded normalized scalar adjunction.
Source: Stacks 08J9, 03CZ (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def restrictedComparison (K L : DerivedCategory (scalarModules J R)) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj L)) :=
  (scalarDerivedRestriction a).map (comparison M μ a K L) ≫
    (α.iso a).hom.app (op K, (M.scalar a).derived.obj L)

/-- The exact-extension representative map, using the universal derived counit and
termwise restriction comparison. Its invertibility under exactness is asserted below.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def representative
    (ν : ScalarTensorIdentification M a)
    (B : CochainComplex (scalarModules J R) ℤ) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj (DerivedCategory.Q.obj B)) ⟶
      DerivedCategory.Q.obj ((scalarTensor.{c, v, r} a).obj B) :=
  (scalarDerivedRestriction a).map
      (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
        (M.scalar a).derived (M.scalar a).counit B) ≫
    (scalarRestrictionComparison a).hom.app
      ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj B) ≫
    DerivedCategory.Q.map (ν.inv.app B)

/-- The source identification U E^L H_R(QP,QC) to Q(S tensor Hom(P,I(C))).
Source: Stacks 0A95, 06YY (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def sourceMap
    (ν : ScalarTensorIdentification M a)
    (P L : CochainComplex (scalarModules J R) ℤ) :
    (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj
      ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L))) ⟶
      DerivedCategory.Q.obj ((scalarTensor.{c, v, r} a).obj
        ((homFixed.{c, v, r} J R P).obj L)) :=
  (scalarDerivedRestriction a).map ((M.scalar a).derived.map
      (coefficientHomResolutionIso.{r, c, v, w} J R P L).hom) ≫
    representative M a ν ((homFixed.{c, v, r} J R P).obj L)

/-- The target identification H_R(QP,U E^L QC) to Q(Hom(P,I(S tensor C))).
Source: Stacks 0A95, 06YY (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def targetMap
    (ν : ScalarTensorIdentification M a)
    (P L : CochainComplex (scalarModules J R) ℤ) :
    (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
      (op (DerivedCategory.Q.obj P),
        (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj (DerivedCategory.Q.obj L))) ⟶
      DerivedCategory.Q.obj ((homFixed.{c, v, r} J R P).obj
        ((scalarTensor.{c, v, r} a).obj L)) :=
  (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) (representative M a ν L)) ≫
    (coefficientHomResolutionIso.{r, c, v, w} J R P ((scalarTensor.{c, v, r} a).obj L)).hom

/-- The strict denominator v_S = Hom(P,I(S tensor eta_C)), without changing models.
Source: Stacks 0A95 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def denominator
    (P L : CochainComplex (scalarModules J R) ℤ) :
    (homFixed.{c, v, r} J R P).obj ((scalarTensor.{c, v, r} a).obj L) ⟶
      (homFixed.{c, v, r} J R P).obj ((scalarTensor.{c, v, r} a).obj
        ((coefficientHomResolution.{r, c, v} J R).obj L)) :=
  roofDenominator.{c, v, r} J R P L
    ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))

/-- The strict numerator a_S is the component of the unique normalized comparison.
Source: Stacks 08J9, 03CZ (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def numerator
    (P L : CochainComplex (scalarModules J R) ℤ) :
    (scalarTensor.{c, v, r} a).obj ((homFixed.{c, v, r} J R P).obj L) ⟶
      (homFixed.{c, v, r} J R P).obj ((scalarTensor.{c, v, r} a).obj
        ((coefficientHomResolution.{r, c, v} J R).obj L)) :=
  (WeilConjectures.SfbHomFilteredColimit.comparison.{c, v, r} J R P L).app
    ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)))

/-- Inverting precisely the localized denominator; the argument supplies only its proof
of being a quasi-isomorphism, with no choice of any map or object.
Source: Stacks 0A95 (blueprint: lem-sfb-hom-flat-evaluation-roof). -/
noncomputable def denominatorInverse
    (P L : CochainComplex (scalarModules J R) ℤ) (hv : QuasiIso (denominator.{c, v, r} a P L)) :
    DerivedCategory.Q.obj ((homFixed.{c, v, r} J R P).obj
      ((scalarTensor.{c, v, r} a).obj ((coefficientHomResolution.{r, c, v} J R).obj L))) ⟶
    DerivedCategory.Q.obj ((homFixed.{c, v, r} J R P).obj
      ((scalarTensor.{c, v, r} a).obj L)) :=
  letI := hv
  inv (DerivedCategory.Q.map (denominator.{c, v, r} a P L))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `tensorIso_normalized` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofTensorNormalized (ν : ScalarTensorComparisons M) : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
  (B : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (V : Cᵒᵖ)
  (s : S.obj.obj V) (x : (B.X n).val.obj V),
  (((ν a).hom.app B).f n).val.app V
      (tensorGenerator.{c, v, r} J R _ B n V s x) =
    ((eqToHom ((M.scalar a).extension_obj (B.X n)).symm).val.app V)
      ((toSheafify J (changeOfRingsPresheaf a (B.X n)).presheaf).app V
        (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `exact_computes` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofExactComputes : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
  PreservesFiniteLimits (M.scalar a).extension →
  ∀ B : CochainComplex (scalarModules J R) ℤ,
    IsIso (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
      (M.scalar a).derived (M.scalar a).counit B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `denominator_quasiIso` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofDenominatorQuasiIso : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
  PreservesFiniteLimits (M.scalar a).extension →
  ∀ (P L : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    QuasiIso (denominator.{c, v, r} a P L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `equation` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofEquation (ν : ScalarTensorComparisons M) : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
  PreservesFiniteLimits (M.scalar a).extension →
  ∀ (P L : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) ≫
        targetMap M a (ν a) P L ≫ DerivedCategory.Q.map (denominator.{c, v, r} a P L) =
      sourceMap M a (ν a) P L ≫ DerivedCategory.Q.map (numerator.{c, v, r} a P L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `roof` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofFormula (ν : ScalarTensorComparisons M) : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
  PreservesFiniteLimits (M.scalar a).extension →
  ∀ (P L : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    ∀ hv : QuasiIso (denominator.{c, v, r} a P L),
      restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) ≫
          targetMap M a (ν a) P L =
        sourceMap M a (ν a) P L ≫ DerivedCategory.Q.map (numerator.{c, v, r} a P L) ≫
          denominatorInverse.{c, v, r, w} a P L hv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `naturality` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofNaturality : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
  (K K' L L' : DerivedCategory (scalarModules J R)) (f : K' ⟶ K) (g : L ⟶ L'),
  (scalarDerivedRestriction a).map ((M.scalar a).derived.map
      ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom f.op g))) ≫
      restrictedComparison M μ α a K' L' =
    restrictedComparison M μ α a K L ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom f.op ((scalarDerivedRestriction a).map ((M.scalar a).derived.map g)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged `coefficients` condition, shared by the roof declarations.
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
def RoofCoefficients : Prop :=
  ∀ {R S T : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ T)
  (K L : DerivedCategory (scalarModules J R)),
  comparison M μ (a ≫ b) K L =
    (scalarHomExtensionComp M a b).inv.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
      (M.scalar b).derived.map (comparison M μ a K L) ≫
        comparison M μ b ((M.scalar a).derived.obj K) ((M.scalar a).derived.obj L) ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J T).map
            (Prod.mkHom ((scalarHomExtensionComp M a b).inv.app K).op
              ((scalarHomExtensionComp M a b).hom.app L))

section RoofStructure

attribute [local irreducible] RoofTensorNormalized RoofExactComputes
  RoofDenominatorQuasiIso RoofEquation RoofFormula RoofNaturality RoofCoefficients

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full flat evaluation-roof assertion, simultaneously for every coefficient map.
The natural isomorphism nu is fixed by its actual pure-tensor formula. The remaining
fields are propositions about the recorded models and explicitly defined maps.
Coefficient composition includes identity maps and, by the two paths in a commutative
square, arbitrary compatible coefficient maps.
Source: Stacks 08J9, 0A95, 03CZ and the node's evaluation-roof refinement
(blueprint: lem-sfb-hom-flat-evaluation-roof). -/
structure EvaluationRoof where
  /-- The canonical tensor/restricted-extension identification, before localization. -/
  tensorIso : ScalarTensorComparisons M
  /-- On actual sheafified generators, nu sends s tensor x to s tensor x. -/
  tensorIso_normalized : RoofTensorNormalized M tensorIso
  /-- Exact ordinary extension computes derived extension on every complex. -/
  exact_computes : RoofExactComputes M
  /-- No boundedness or continuity is needed for the strict denominator. -/
  denominator_quasiIso : RoofDenominatorQuasiIso M
  /-- The equation [v_S] Theta U(c) = [a_S], with both representative transports. -/
  equation : RoofEquation M μ α tensorIso
  /-- Equivalently Theta U(c) is the numerator followed by the inverse denominator. -/
  roof : RoofFormula M μ α tensorIso
  /-- Naturality in both derived inputs, including maps represented by inverse quasi-isos. -/
  naturality : RoofNaturality M μ α
  /-- Coefficient compatibility, with the unit-normalized scalar composition transports. -/
  coefficients : RoofCoefficients M μ

end RoofStructure

attribute [local implicit_reducible] RoofTensorNormalized RoofExactComputes
  RoofDenominatorQuasiIso RoofEquation RoofFormula RoofNaturality RoofCoefficients

attribute [local implicit_reducible] scalarTensor numerator denominator
attribute [local semireducible] coefficientTotalTensor

open CategoryTheory.MonoidalCategory


attribute [local irreducible] CoefficientTensorModels.iso

attribute [local irreducible] derivedInternalHomOfUniverses DerivedCategory.Q
  scalarDerivedRestriction scalarRestrictionComparison

attribute [local irreducible] _root_.instCategoryDerivedCategory
  SheafOfModules.instPreadditive PresheafOfModules.instPreadditive

attribute [local irreducible] singleTensorIso CochainComplex.mapBifunctorSingle₁Iso

attribute [local irreducible] coefficientTensorGenerator

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionBifunctor_map
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ B) (G : B ⥤ D ⥤ E) (X : A) {Y Y' : D} (f : Y ⟶ Y') :
    (Prod.sectR X D ⋙ (F.prod (𝟭 D) ⋙ Functor.uncurry.obj G)).map f =
      (G.obj (F.obj X)).map f := by
  dsimp [Prod.sectR]
  simp only [Functor.map_id, NatTrans.id_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[no_expose] private noncomputable def singleScalarIso :
    @Iso (CochainComplex (scalarModules J R) ℤ ⥤ CochainComplex (scalarModules J R) ℤ)
      _ (scalarTensor.{c, v, r} a) (StrictScalarHom.tensor.{c, v, r} a) := by
  let := SheafOfModules.monoidalCategory R
  unfold StrictScalarHom.tensor StrictScalarHom.scalarModule
    SheafOfModules.cochainModulesMonoidal
  let T := (scalarRestriction a).obj (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  refine NatIso.ofComponents (fun B ↦ singleTensorIso.{c, v, r} J R T B) ?_
  intro B B' f
  have hs : (scalarTensor.{c, v, r} a).map f =
      (((curriedTensor (scalarModules J R)).map₂HomologicalComplex (.up ℤ) (.up ℤ)
        (.up ℤ)).obj ((HomologicalComplex.single _ (.up ℤ) 0).obj T)).map f := by
    exact sectionBifunctor_map (HomologicalComplex.single _ (.up ℤ) 0)
      ((curriedTensor (scalarModules J R)).map₂HomologicalComplex (.up ℤ) (.up ℤ)
        (.up ℤ)) T f
  rw [hs]
  simpa only [CochainComplex.map₂HomologicalComplexObjSingleIso_hom_app, singleTensorIso]
    using (CochainComplex.map₂HomologicalComplexObjSingleIso
      (curriedTensor (scalarModules J R)) T).hom.naturality f

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem singleScalarIso_pure
    (B : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (B.X n).val.obj V) :
    (((singleScalarIso.{c, v, r} a).hom.app B).f n).val.app V
      (tensorGenerator.{c, v, r} J R _ B n V s x) =
        StrictScalarHom.tensorSection.{c, v, r} a B n V s x := by
  change ((singleTensorIso.{c, v, r} J R _ B).hom.f n).val.app V _ = _
  rw [tensorGenerator_hom.{c, v, r} J R]
  unfold StrictScalarHom.tensorSection WeilConjectures.SfbHomFilteredColimit.pure
    tensorSectionMap
  rfl

@[no_expose] private noncomputable def totalScalarIso (E : FlatScalarEvaluation.Representatives M) :
    ScalarTensorIdentification M a :=
  singleScalarIso.{c, v, r} a ≪≫ E.nu a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem totalScalarIso_pure (E : FlatScalarEvaluation.Representatives M) :
    RoofTensorNormalized M (fun a ↦ totalScalarIso.{c, v, r, w} M a E) := by
  intro R S a B n V s x
  change (((E.nu a).hom.app B).f n).val.app V
    (((singleScalarIso.{c, v, r} a).hom.app B).f n |>.val.app V
      (tensorGenerator.{c, v, r} J R _ B n V s x)) = _
  rw [singleScalarIso_pure.{c, v, r} a]
  rw [E.nu_pure]
  dsimp only [FlatScalarEvaluation.extensionSection, scalarHomUnitSection]
  have hu := congrArg
    (fun y ↦ ((eqToHom ((M.scalar a).extension_obj (B.X n)).symm).val.app V) y)
    ((M.scalar a).ordinaryUnit (B.X n) V x)
  simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hu
  rw [hu, ← map_smul]
  congr 1
  change s • ((PresheafOfModules.toSheafify (𝟙 _)
    (toSheafify J (changeOfRingsPresheaf a (B.X n)).presheaf)).app V)
      ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x) = _
  rw [← map_smul]
  change ((toSheafify J (changeOfRingsPresheaf a (B.X n)).presheaf).app V)
    ((s * 1) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x) = _
  rw [mul_one]

attribute [local irreducible] singleScalarIso totalScalarIso
  FlatScalarEvaluation.extensionSection StrictScalarHom.tensorSection

attribute [local irreducible] coefficientTotalTensor

attribute [local implicit_reducible] homComplex scalarComplex
  coefficientHomResolution scalarHomSource scalarHomTarget
  StrictScalarHom.restriction
  StrictScalarHom.tensor StrictScalarHom.scalarModule
  WeilConjectures.SfbHomFilteredColimit.tensorFixed
  WeilConjectures.SfbHomFilteredColimit.tensor

section ResolutionHelperProofs

attribute [local semireducible] derivedInternalHomOfUniverses DerivedCategory.Q

attribute [local semireducible] _root_.instCategoryDerivedCategory
  SheafOfModules.instPreadditive PresheafOfModules.instPreadditive

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
private theorem resolutionUnit_quasiIso (L : CochainComplex (scalarModules J R) ℤ) :
    QuasiIso ((resolutionUnit.{c, v, r} J R).app L) := by
  let :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  exact (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} _ L).2

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
private theorem resolution_obj_isKInjective (L : CochainComplex (scalarModules J R) ℤ) :
    ((coefficientHomResolution.{r, c, v} J R).obj L).IsKInjective := by
  let :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  exact CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ _

private theorem resolutionInverse_eq (L : CochainComplex (scalarModules J R) ℤ)
    [QuasiIso ((resolutionUnit.{c, v, r} J R).app L)] :
    coefficientHomResolutionInverse.{r, c, v, w} J R L =
      inv (DerivedCategory.Q.map ((resolutionUnit.{c, v, r} J R).app L)) := by
  rfl

end ResolutionHelperProofs

attribute [local irreducible] coefficientHomResolution coefficientHomResolutionIso
  coefficientHomResolutionInverse resolutionUnit

private theorem scalarTensor_quasiIso (E : FlatScalarEvaluation.Representatives M)
    (ha : PreservesFiniteLimits (M.scalar a).extension)
    {B B' : CochainComplex (scalarModules J R) ℤ} (f : B ⟶ B') (hf : QuasiIso f) :
    QuasiIso ((scalarTensor.{c, v, r} a).map f) := by
  let := ha
  let := (M.scalar a).extension_additive
  let := (M.scalar a).ordinaryAdjunction.isLeftAdjoint
  let := hf
  have hmap : QuasiIso ((scalarComplex (M.scalar a).extension
      (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ)).map f) := by
    change QuasiIso (((scalarRestriction a).mapHomologicalComplex (.up ℤ)).map
      (((M.scalar a).extension.mapHomologicalComplex (.up ℤ)).map f))
    infer_instance
  have hn := (totalScalarIso.{c, v, r, w} M a E).hom.naturality f
  have : QuasiIso ((scalarTensor.{c, v, r} a).map f ≫
      (totalScalarIso.{c, v, r, w} M a E).hom.app B') := by
    rw [hn]
    let := hmap
    infer_instance
  exact quasiIso_of_comp_right _ ((totalScalarIso.{c, v, r, w} M a E).hom.app B')

private theorem denominator_quasiIso_proof (E : FlatScalarEvaluation.Representatives M) :
    RoofDenominatorQuasiIso M := by
  intro R S a ha P L _ _
  have hη (B : CochainComplex (scalarModules J R) ℤ) :
      QuasiIso ((resolutionUnit.{c, v, r} J R).app B) :=
    resolutionUnit_quasiIso.{c, v, r} B
  let f := (scalarTensor.{c, v, r} a).map ((resolutionUnit.{c, v, r} J R).app L)
  have hf : QuasiIso f := scalarTensor_quasiIso M a E ha _ (hη L)
  let I := coefficientHomResolution.{r, c, v} J R
  have hnat : f ≫ (resolutionUnit.{c, v, r} J R).app
      ((scalarTensor.{c, v, r} a).obj (I.obj L)) =
        (resolutionUnit.{c, v, r} J R).app ((scalarTensor.{c, v, r} a).obj L) ≫ I.map f :=
    (resolutionUnit.{c, v, r} J R).naturality f
  have : QuasiIso f := hf
  have : QuasiIso ((resolutionUnit.{c, v, r} J R).app
      ((scalarTensor.{c, v, r} a).obj L)) := hη _
  have : QuasiIso ((resolutionUnit.{c, v, r} J R).app
      ((scalarTensor.{c, v, r} a).obj (I.obj L))) := hη _
  have : QuasiIso ((resolutionUnit.{c, v, r} J R).app
      ((scalarTensor.{c, v, r} a).obj L) ≫ I.map f) := by
    rw [← hnat]
    dsimp
    infer_instance
  have : QuasiIso (I.map f) :=
    quasiIso_of_comp_left ((resolutionUnit.{c, v, r} J R).app
      ((scalarTensor.{c, v, r} a).obj L)) (I.map f)
  have : (I.obj ((scalarTensor.{c, v, r} a).obj L)).IsKInjective :=
    resolution_obj_isKInjective.{c, v, r} _
  have : (I.obj ((scalarTensor.{c, v, r} a).obj (I.obj L))).IsKInjective :=
    resolution_obj_isKInjective.{c, v, r} _
  have hh := quasiIso_homComplex_mapOfUniverses.{c, v, r}
    (I' := I.obj ((scalarTensor.{c, v, r} a).obj L))
    (I := I.obj ((scalarTensor.{c, v, r} a).obj (I.obj L))) (I.map f) (𝟙 P)
  change QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map (I.map f))
  simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] using hh


@[no_expose] private noncomputable def fixedDerivedHom (P : CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J R) where
  obj K := (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
    (op (DerivedCategory.Q.obj P), K)
  map f := (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
    (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) f)
  map_id K := (derivedInternalHomOfUniverses.{c, v, r, w} J R).map_id _
  map_comp f g := by
    rw [← Functor.map_comp]
    congr 1
    apply CategoryTheory.Prod.hom_ext
    · exact (Category.id_comp _).symm
    · rfl

attribute [local implicit_reducible] fixedDerivedHom

private theorem restrictedComparison_natural
    (E : FlatScalarEvaluation.DerivedCoherence M μ) : RoofNaturality M μ α := by
  intro R S a K K' L L' f g
  dsimp only [restrictedComparison]
  rw [← Category.assoc, ← Functor.map_comp]
  have hn := E.naturality a K L K' L' f g
  change _ ≫ comparison M μ a K' L' = comparison M μ a K L ≫ _ at hn
  rw [hn, Functor.map_comp, Category.assoc]
  have hα := (α.iso a).hom.naturality
    (Prod.mkHom f.op ((M.scalar a).derived.map g))
  change (scalarDerivedRestriction a).map
      ((derivedInternalHomOfUniverses.{c, v, r, w} J S).map
        (Prod.mkHom ((M.scalar a).derived.map f).op ((M.scalar a).derived.map g))) ≫
        (α.iso a).hom.app (op K', (M.scalar a).derived.obj L') =
    (α.iso a).hom.app (op K, (M.scalar a).derived.obj L) ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom f.op ((scalarDerivedRestriction a).map ((M.scalar a).derived.map g))) at hα
  rw [Category.assoc]
  exact congrArg ((scalarDerivedRestriction a).map (comparison M μ a K L) ≫ ·) hα

attribute [local semireducible] coefficientTotalTensor

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
@[no_expose] private noncomputable def totalInclusion
    (D P : CochainComplex (scalarModules J R) ℤ)
    (n p k : ℤ) (h : n + p = k) :
    letI := SheafOfModules.monoidalCategory R
    D.X n ⊗ P.X p ⟶ ((coefficientTotalTensor.{r, c, v} J R).obj (D, P)).X k := by
  let := SheafOfModules.monoidalCategory R
  exact HomologicalComplex.ιMapBifunctor D P (curriedTensor _) (.up ℤ) n p k h

section TotalGeneratorEquation
attribute [local semireducible] coefficientTensorGenerator

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
private theorem totalGenerator_eq
    (D P : CochainComplex (scalarModules J R) ℤ)
    (n p k : ℤ) (h : n + p = k) (V : Cᵒᵖ)
    (x : (D.X n).val.obj V) (y : (P.X p).val.obj V) :
    letI := SheafOfModules.monoidalCategory R
    coefficientTensorGenerator.{r, c, v} J R D P n p k h V x y =
      (totalInclusion.{c, v, r} D P n p k h).val.app V
        (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R (D.X n) (P.X p) V x y) := by
  rfl

end TotalGeneratorEquation

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
private theorem total_map_eq
    {D D' P P' : CochainComplex (scalarModules J R) ℤ}
    (f : D ⟶ D') (g : P ⟶ P') :
    letI := SheafOfModules.monoidalCategory R
    (coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom f g) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ) := by
  exact ScalarHomTensor.tensorMap_factor f g


omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
private theorem totalInclusion_natural
    {D D' P P' : CochainComplex (scalarModules J R) ℤ}
    (f : D ⟶ D') (g : P ⟶ P') (n p k : ℤ) (h : n + p = k) :
    letI := SheafOfModules.monoidalCategory R
    (f.f n ⊗ₘ g.f p) ≫ totalInclusion.{c, v, r} D' P' n p k h =
      totalInclusion.{c, v, r} D P n p k h ≫
        ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom f g)).f k := by
  let := SheafOfModules.monoidalCategory R
  have hi := HomologicalComplex.ι_mapBifunctorMap f g
    (curriedTensor _) (.up ℤ) n p k h
  simp only [MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map] at hi
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def] at hi
  rw [total_map_eq.{c, v, r}]
  exact hi.symm

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
private theorem totalGenerator_map
    {D D' P P' : CochainComplex (scalarModules J R) ℤ}
    (f : D ⟶ D') (g : P ⟶ P') (n p k : ℤ) (h : n + p = k)
    (V : Cᵒᵖ) (x : (D.X n).val.obj V) (y : (P.X p).val.obj V) :
    (((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom f g)).f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J R D P n p k h V x y) =
    coefficientTensorGenerator.{r, c, v} J R D' P' n p k h V
      ((f.f n).val.app V x) ((g.f p).val.app V y) := by
  let := SheafOfModules.monoidalCategory R
  rw [totalGenerator_eq, totalGenerator_eq]
  have hh := congrArg (fun z ↦ z.val.app V
    (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R (D.X n) (P.X p) V x y))
    (totalInclusion_natural.{c, v, r} f g n p k h).symm
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hh
  exact hh.trans (congrArg ((totalInclusion.{c, v, r} D' P' n p k h).val.app V)
    (pure_map.{c, v, r} J R (f.f n) (g.f p) V x y))

section PureGenerators

attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pure_three_ext (A B D H : scalarModules J R) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (f g : (A ⊗ B) ⊗ D ⟶ H),
    (∀ (V : Cᵒᵖ) (x : A.val.obj V) (y : B.val.obj V) (z : D.val.obj V),
      f.val.app V (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R (A ⊗ B) D V
        (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R A B V x y) z) =
      g.val.app V (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R (A ⊗ B) D V
        (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R A B V x y) z)) → f = g := by
  let := SheafOfModules.monoidalCategory R
  intro f g h
  let RR := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 RR.obj)
  let Sh := PresheafOfModules.sheafification (𝟙 RR.obj)
  let W := J.W.inverseImage (PresheafOfModules.toPresheaf RR.obj)
  let φ := tensorSectionMap.{c, v, r} J R A B
  have hη : W (adj.unit.app (A.val ⊗ B.val)) := by
    dsimp only [W]
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 RR.obj)]
    change IsIso (Sh.map (adj.unit.app (A.val ⊗ B.val)))
    dsimp only [adj]
    infer_instance
  have hi : IsIso (tensorObjIsoSheafification A B).inv.val := by
    change IsIso ((SheafOfModules.forget RR).map
      (tensorObjIsoSheafification A B).inv)
    infer_instance
  have hφ : W φ := W.comp_mem _ _ hη (W.of_isIso _)
  have hφD : W (φ ▷ D.val) := W.whiskerRight_mem φ hφ D.val
  have hiD : IsIso (Sh.map (φ ▷ D.val)) := by
    dsimp only [W] at hφD
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 RR.obj)] at hφD
    exact hφD
  apply (cancel_epi (tensorObjIsoSheafification (A ⊗ B) D).inv).mp
  apply (cancel_epi (Sh.map (φ ▷ D.val))).mp
  apply (adj.homEquiv _ H).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro x y z
  exact h V x y z


omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem doubleGenerator_ext
    (T : scalarModules J R) (B P H : CochainComplex (scalarModules J R) ℤ)
    (f g : (coefficientTotalTensor.{r, c, v} J R).obj
      ((WeilConjectures.SfbHomFilteredColimit.tensor.{c, v, r} J R).obj (T, B), P) ⟶ H)
    (h : ∀ (n p k : ℤ) (hn : n + p = k) (V : Cᵒᵖ)
      (s : T.val.obj V) (x : (B.X n).val.obj V) (y : (P.X p).val.obj V),
      (f.f k).val.app V (coefficientTensorGenerator.{r, c, v} J R _ P n p k hn V
        (tensorGenerator.{c, v, r} J R T B n V s x) y) =
      (g.f k).val.app V (coefficientTensorGenerator.{r, c, v} J R _ P n p k hn V
        (tensorGenerator.{c, v, r} J R T B n V s x) y)) : f = g := by
  let := SheafOfModules.monoidalCategory R
  apply HomologicalComplex.hom_ext
  intro k
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro n p hn
  let q : T ⊗ B.X n ⟶
      ((WeilConjectures.SfbHomFilteredColimit.tensor.{c, v, r} J R).obj (T, B)).X n :=
    (singleTensorIso.{c, v, r} J R T B).inv.f n
  have : IsIso q := by dsimp only [q]; infer_instance
  apply (cancel_epi (q ▷ P.X p)).mp
  apply pure_three_ext.{c, v, r} T (B.X n) (P.X p) (H.X k)
  intro V s x y
  have hmap := pure_map.{c, v, r} J R
    q (𝟙 (P.X p)) V
      (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R T (B.X n) V s x) y
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply, MonoidalCategory.tensorHom_id] at hmap
  let ι := totalInclusion.{c, v, r}
    ((WeilConjectures.SfbHomFilteredColimit.tensor.{c, v, r} J R).obj (T, B)) P n p k hn
  change (f.f k).val.app V (ι.val.app V
    ((q ▷ P.X p).val.app V
      (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R (T ⊗ B.X n)
        (P.X p) V (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r}
          J R T (B.X n) V s x) y))) =
    (g.f k).val.app V (ι.val.app V
    ((q ▷ P.X p).val.app V
      (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R (T ⊗ B.X n)
        (P.X p) V (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r}
          J R T (B.X n) V s x) y)))
  rw [hmap]
  have hq : q.val.app V
      (WeilConjectures.SfbHomFilteredColimit.pure.{c, v, r} J R T (B.X n) V s x) =
      tensorGenerator.{c, v, r} J R T B n V s x :=
    (tensorGenerator_eq.{c, v, r} J R T B n V s x).symm
  rw [hq]
  simpa only [totalGenerator_eq] using h n p k hn V s x y

end PureGenerators

attribute [local irreducible] totalInclusion

attribute [local irreducible] coefficientTotalTensor

section ResolutionNaturalityProof

attribute [local semireducible] derivedInternalHomOfUniverses DerivedCategory.Q
  scalarDerivedRestriction scalarRestrictionComparison

private theorem homResolution_natural (P : CochainComplex (scalarModules J R) ℤ)
    {B B' : CochainComplex (scalarModules J R) ℤ} (f : B ⟶ B') :
    (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) (DerivedCategory.Q.map f)) ≫
      (coefficientHomResolutionIso.{r, c, v, w} J R P B').hom =
    (coefficientHomResolutionIso.{r, c, v, w} J R P B).hom ≫
      DerivedCategory.Q.map ((homFixed.{c, v, r} J R P).map f) := by
  dsimp only [homFixed, Functor.comp_map]
  have he := RingedHomUniverses.resolutionComparison_naturality.{c, v, r, w} J R
    (op P, B) (op P, B') (Prod.mkHom (𝟙 (op P)) f)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.op_map,
    Functor.comp_obj, Functor.prod_obj, Functor.op_obj, Functor.id_obj,
    RingedHomUniverses.ordinaryBifunctor, Functor.uncurry_obj_map] at he
  simpa only [unop_id, Functor.map_id, op_id, NatTrans.id_app, Category.id_comp] using he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pairComparison_natural
    {B B' : CochainComplex (scalarModules J R) ℤ} (f : B ⟶ B') :
    (M.scalar a).derived.map (DerivedCategory.Q.map f) ≫
      scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
        (M.scalar a).derived (M.scalar a).counit B' =
    scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
        (M.scalar a).derived (M.scalar a).counit B ≫
      DerivedCategory.Q.map
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map f) := by
  have hc := (M.scalar a).counit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map f)
  unfold scalarPairComplexComparison
  have hq := (DerivedCategory.quotientCompQhIso (scalarModules J R)).inv.naturality f
  have hq' := (DerivedCategory.quotientCompQhIso (scalarModules J S)).hom.naturality
    ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map f)
  dsimp only [Functor.comp_map] at hc hq hq'
  rw [← Category.assoc, ← (M.scalar a).derived.map_comp, hq,
    (M.scalar a).derived.map_comp, Category.assoc, ← Category.assoc _ _
      ((DerivedCategory.quotientCompQhIso (scalarModules J S)).hom.app _), hc]
  simp only [Category.assoc]
  exact congrArg ((M.scalar a).derived.map
    ((DerivedCategory.quotientCompQhIso (scalarModules J R)).inv.app B) ≫
      (M.scalar a).counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj B) ≫ ·) hq'

private theorem representative_natural (ν : ScalarTensorIdentification M a)
    {B B' : CochainComplex (scalarModules J R) ℤ} (f : B ⟶ B') :
    (scalarDerivedRestriction a).map ((M.scalar a).derived.map (DerivedCategory.Q.map f)) ≫
      representative M a ν B' =
    representative M a ν B ≫ DerivedCategory.Q.map ((scalarTensor.{c, v, r} a).map f) := by
  have hc := pairComparison_natural M a f
  have hr := (scalarRestrictionComparison a).hom.naturality
    ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map f)
  have hn := ν.inv.naturality f
  dsimp only [Functor.comp_map] at hr hn
  dsimp only [representative]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, hc, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (DerivedCategory.Q.map _), hr]
  simp only [Category.assoc]
  rw [← DerivedCategory.Q.map_comp, hn, DerivedCategory.Q.map_comp]

end ResolutionNaturalityProof

section Closed
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
  (T : CoefficientClosedStructure H)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem uncurry_pre {A B K L : D} (f : A ⟶ B) (g : B ⟶ H.obj (op K, L)) :
    (T.transpose A K L).symm (f ≫ g) =
      T.tensor.map (Prod.mkHom f (𝟙 K)) ≫ (T.transpose B K L).symm g := by
  let := T.monoidal
  change ((T.adjunction K).homEquiv A L).symm (f ≫ g) = _
  rw [Adjunction.homEquiv_naturality_left_symm]
  change (f ▷ K) ≫ _ = (f ⊗ₘ 𝟙 K) ≫ _
  rw [tensorHom_id]
  rfl
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem uncurry_post {A K L L' : D} (g : A ⟶ H.obj (op K, L)) (f : L ⟶ L') :
    (T.transpose A K L').symm (g ≫ H.map (Prod.mkHom (𝟙 (op K)) f)) =
      (T.transpose A K L).symm g ≫ f := by
  let := T.monoidal
  change ((T.adjunction K).homEquiv A L').symm
    (g ≫ (Prod.sectR (op K) D ⋙ H).map f) = _
  rw [Adjunction.homEquiv_naturality_right_symm]
  rfl
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem uncurry_pre_post {A B K L L' : D} (s : A ⟶ B)
    (g : B ⟶ H.obj (op K, L)) (u : L ⟶ L') :
    (T.transpose A K L').symm (s ≫ g ≫ H.map (Prod.mkHom (𝟙 (op K)) u)) =
      T.tensor.map (Prod.mkHom s (𝟙 K)) ≫ (T.transpose B K L).symm g ≫ u := by
  rw [← Category.assoc s g, uncurry_post, uncurry_pre, Category.assoc]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transpose_from_evaluation
    {A X K L L' : D} (i : X ≅ T.tensor.obj (A, K))
    (f : A ⟶ H.obj (op K, L)) (e : X ⟶ L') (u : L ⟶ L') [IsIso u]
    (he : i.hom ≫ T.tensor.map (Prod.mkHom f (𝟙 K)) ≫ T.evaluation K L =
      e ≫ inv u) :
    T.transpose A K L' (i.inv ≫ e) = f ≫ H.map (Prod.mkHom (𝟙 (op K)) u) := by
  apply (T.transpose A K L').symm.injective
  rw [Equiv.symm_apply_apply, uncurry_post, ClosedScalarHom.uncurry_formula]
  apply (cancel_epi i.hom).mp
  rw [Iso.hom_inv_id_assoc]
  calc
    e = (e ≫ inv u) ≫ u := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    _ = _ := by rw [← he]; simp only [Category.assoc]
end Closed

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem map_composition_equality
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y Z W : A} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ W} {i : W ⟶ Z}
    (e : f ≫ g = h ≫ i) : F.map f ≫ F.map g = F.map h ≫ F.map i := by
  simpa only [Functor.map_comp] using F.congr_map e

private theorem conjugate_inverse {D : Type*} [Category D] {A B C X : D}
    (l : A ⟶ B) (r : B ⟶ A) (j : C ≅ X) (f : A ⟶ C) (g : B ⟶ X)
    (h : l ≫ g = f ≫ j.hom) (hi : r ≫ l = 𝟙 B) :
    g ≫ j.inv = r ≫ f := by
  calc
    _ = r ≫ (l ≫ g) ≫ j.inv := by
      simp only [← Category.assoc, hi, Category.id_comp]
    _ = _ := by rw [h]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

section TransposeDiagram
variable {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
  (T : CoefficientClosedStructure H)
private theorem resolved_diagram {A B C P I J X Y : D}
    (s : A ⟶ B) [IsIso s] (r : B ⟶ C) (q : A ⟶ C)
    (g : B ⟶ H.obj (op P, I)) (e : I ⟶ J) (u : J ⟶ X)
    (n : C ⟶ H.obj (op P, X))
    (i : Y ≅ T.tensor.obj (A, P)) (Z : D) (j : Z ≅ T.tensor.obj (C, P))
    (t : Y ⟶ Z) (h : Y ⟶ J) (v : Z ⟶ X)
    (hs : s ≫ r = q)
    (hc : i.hom ≫ T.tensor.map (Prod.mkHom s (𝟙 P)) ≫
      (T.transpose B P I).symm g ≫ e = h)
    (hn : t ≫ j.hom = i.hom ≫ T.tensor.map (Prod.mkHom q (𝟙 P)))
    (ht : j.hom ≫ (T.transpose C P X).symm n = v)
    (hh : h ≫ u = t ≫ v) :
    g ≫ H.map (Prod.mkHom (𝟙 (op P)) (e ≫ u)) = r ≫ n := by
  apply (cancel_epi s).mp
  simp only [← Category.assoc, hs]
  simp only [Category.assoc]
  apply (T.transpose A P X).symm.injective
  apply (cancel_epi i.hom).mp
  rw [uncurry_pre_post, uncurry_pre]
  calc
    _ = h ≫ u := by
      simpa only [Category.assoc] using congrArg (· ≫ u) hc
    _ = t ≫ v := hh
    _ = _ := by
      rw [← ht, ← Category.assoc, hn]
      simp only [Category.assoc]
end TransposeDiagram

private theorem roof_diagram
    {D : Type*} [Category D] {A B C E F G H I K L : D}
    (u : A ⟶ B) (v : B ⟶ C) (w : A ⟶ C)
    (d : A ⟶ E) (d' : C ⟶ F) (e : E ⟶ F)
    (r : E ⟶ G) (r' : F ⟶ H) (t : G ⟶ H)
    (j : G ⟶ I) (k : H ≅ K) (z : I ⟶ K)
    (b : B ⟶ L) (a : L ⟶ K)
    (hu : u ≫ v = w) (hn : w ≫ d' = d ≫ e)
    (hr : e ≫ r' = r ≫ t) (hh : t ≫ k.hom = j ≫ z)
    (hc : v ≫ d' ≫ r' = b ≫ a ≫ k.inv) :
    d ≫ r ≫ j ≫ z = u ≫ b ≫ a := by
  calc
    _ = d ≫ r ≫ t ≫ k.hom := by rw [hh]
    _ = d ≫ e ≫ r' ≫ k.hom := by
      rw [← Category.assoc r t, ← hr]
      simp only [Category.assoc]
    _ = w ≫ d' ≫ r' ≫ k.hom := by
      rw [← Category.assoc d e, ← hn]
      simp only [Category.assoc]
    _ = u ≫ v ≫ d' ≫ r' ≫ k.hom := by rw [← hu, Category.assoc]
    _ = _ := by
      have hc' := congrArg (fun x ↦ u ≫ x ≫ k.hom) hc
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarEvaluation_transport
    (G : FlatScalarEvaluation.Representatives M)
    (P I : CochainComplex (scalarModules J R) ℤ)
    (e : (coefficientTotalTensor.{r, c, v} J R).obj
      ((scalarTensor.{c, v, r} a).obj (homComplex P I), P) ⟶
        (scalarTensor.{c, v, r} a).obj I)
    (he : ∀ (n p k : ℤ) (hn : n + p = k) (hn' : p + n = k) (V : Cᵒᵖ)
      (s : S.obj.obj V) (x : ((homComplex P I).X n).val.obj V)
      (y : (P.X p).val.obj V),
      (e.f k).val.app V
        (coefficientTensorGenerator.{r, c, v} J R _ P n p k hn V
          (tensorGenerator.{c, v, r} J R _ (homComplex P I) n V s x) y) =
        tensorGenerator.{c, v, r} J R _ I k V s
          (homValue.{c, v, r} J R P I n p k hn' V x y)) :
    (coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom ((singleScalarIso.{c, v, r} a).hom.app (homComplex P I)) (𝟙 P)) ≫
      G.scalarEvaluate a P I (homComplex P I) (𝟙 _) =
        e ≫ (totalScalarIso.{c, v, r, w} M a G).hom.app I := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    refine doubleGenerator_ext.{c, v, r}
      ((scalarRestriction a).obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))
      (homComplex P I) P
      ((StrictScalarHom.restriction.{c, v, r} a).obj
        ((FlatScalarEvaluation.extension M a).obj
          I)) _ _ ?_
    intro n p k hn V s x y
    change S.obj.obj V at s
    change ((G.scalarEvaluate a P _ _ (𝟙 _)).f k).val.app V
      (((((coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom ((singleScalarIso.{c, v, r} a).hom.app _) (𝟙 P))).f k).val.app V
          (coefficientTensorGenerator.{r, c, v} J R _ P n p k hn V
            (tensorGenerator.{c, v, r} J R _ _ n V s x) y))) = _
    erw [totalGenerator_map.{c, v, r}, singleScalarIso_pure.{c, v, r} a
      (homComplex P I) n V s x]
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply]
    erw [G.scalarEvaluate_pure a P
      I
      (homComplex P I) (𝟙 _) n p k hn (by omega) V s x y]
    unfold totalScalarIso
    change _ = (((G.nu a).hom.app _).f k).val.app V
      ((((singleScalarIso.{c, v, r} a).hom.app _).f k).val.app V
      ((e.f k).val.app V _))
    have hvalue := he n p k hn (by omega) V s x y
    have hmap := congrArg (fun z ↦ (((G.nu a).hom.app I).f k).val.app V
      ((((singleScalarIso.{c, v, r} a).hom.app I).f k).val.app V z)) hvalue
    have hsingle := singleScalarIso_pure.{c, v, r} a I k V s
      (homValue.{c, v, r} J R P I n p k (by omega) V x y)
    have hsingle' := congrArg ((((G.nu a).hom.app I).f k).val.app V) hsingle
    have hnu := G.nu_pure a I k V s
      (homValue.{c, v, r} J R P I n p k (by omega) V x y)
    change FlatScalarEvaluation.extensionSection M a I k V s
      (homValue.{c, v, r} J R P I n p k (by omega) V x y) = _
    exact (hmap.trans (hsingle'.trans hnu)).symm

attribute [local irreducible] representative sourceMap

attribute [local irreducible] FlatScalarEvaluation.transpose
  CoefficientClosedStructure.transpose CoefficientClosedStructure.evaluation

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 600000 in
-- The representative transports require a long sequence of categorical rewrites.
private theorem roof_equation
    (G : FlatScalarEvaluation.Representatives M)
    (calculation : FlatScalarEvaluation.Calculation M μ α G)
    (coherence : FlatScalarEvaluation.DerivedCoherence M μ) :
    RoofEquation M μ α (fun a ↦ totalScalarIso.{c, v, r, w} M a G) := by
  intro R S a ha P L hP hp
  obtain ⟨d, hd, hnaturality, hcoefficients⟩ := strict_numerator_transpose.{c, v, r, w, w}
    J R (M.closed R) (M.model R) P L hP hp
  clear hnaturality hcoefficients
  rcases hd with ⟨hTensorNatural, hTensorNormalized, hEvaluationPure, hScalarPure,
    -, -, hEvaluationDerived, hTransposeDerived⟩
  have htensor (B : CochainComplex (scalarModules J R) ℤ) :
    d.tensorIso B = G.tensorIso P hP hp B := by
    obtain ⟨V, t, hV, _, ht, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients B
    have : QuasiIso t := ht
    have : IsIso (DerivedCategory.Q.map t) := inferInstance
    have : IsIso ((M.closed R).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map t) (𝟙 (DerivedCategory.Q.obj P)))) := by
      have : IsIso (Prod.mkHom (DerivedCategory.Q.map t)
          (𝟙 (DerivedCategory.Q.obj P))) :=
        (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
      exact Functor.map_isIso _ _
    have hn := hTensorNatural V B t
    have : IsIso (DerivedCategory.Q.map
        (numeratorTotalMap.{c, v, r} J R t (𝟙 P)) ≫ (d.tensorIso B).hom) := by
      rw [hn]
      infer_instance
    have : IsIso (DerivedCategory.Q.map
        (numeratorTotalMap.{c, v, r} J R t (𝟙 P))) :=
      (isIso_comp_right_iff _ (d.tensorIso B).hom).1 inferInstance
    apply Iso.ext
    apply (cancel_epi (DerivedCategory.Q.map
      (numeratorTotalMap.{c, v, r} J R t (𝟙 P)))).mp
    rw [hn]
    change _ = DerivedCategory.Q.map
      ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom t (𝟙 P))) ≫ _
    rw [G.tensorIso_natural P B V hP hp t,
      hTensorNormalized V hV, G.tensorIso_normalization P V hP hp hV]
  have heval :
    FlatScalarEvaluation.transpose M ((homFixed.{c, v, r} J R P).obj L) P
          ((coefficientHomResolution.{r, c, v} J R).obj L)
          (G.tensorIso P hP hp _) d.evaluation =
        (coefficientHomResolutionIso.{r, c, v, w} J R P L).inv ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
              (DerivedCategory.Q.map ((resolutionUnit.{c, v, r} J R).app L))) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      have : QuasiIso ((resolutionUnit.{c, v, r} J R).app L) :=
        resolutionUnit_quasiIso.{c, v, r} L
      have : IsIso (DerivedCategory.Q.map ((resolutionUnit.{c, v, r} J R).app L)) :=
        inferInstance
      unfold FlatScalarEvaluation.transpose
      have he := hEvaluationDerived
      rw [htensor] at he
      rw [resolutionInverse_eq.{c, v, r, w}] at he
      exact transpose_from_evaluation (M.closed R) (G.tensorIso P hP hp _)
        (coefficientHomResolutionIso.{r, c, v, w} J R P L).inv
        (DerivedCategory.Q.map d.evaluation)
        (DerivedCategory.Q.map ((resolutionUnit.{c, v, r} J R).app L)) he
  have hc :
    (scalarDerivedRestriction a).map ((M.scalar a).derived.map
            (FlatScalarEvaluation.transpose M ((homFixed.{c, v, r} J R P).obj L) P
              ((coefficientHomResolution.{r, c, v} J R).obj L)
              (G.tensorIso P hP hp _) d.evaluation)) ≫
          restrictedComparison M μ α a (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj ((coefficientHomResolution.{r, c, v} J R).obj L)) ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
              (representative M a (totalScalarIso.{c, v, r, w} M a G)
                ((coefficientHomResolution.{r, c, v} J R).obj L))) =
        representative M a (totalScalarIso.{c, v, r, w} M a G)
          ((homFixed.{c, v, r} J R P).obj L) ≫
          DerivedCategory.Q.map (numerator.{c, v, r} a P L) ≫
            (coefficientHomResolutionIso.{r, c, v, w} J R P ((scalarTensor.{c, v, r} a).obj
              ((coefficientHomResolution.{r, c, v} J R).obj L))).inv := by
    let B := (homFixed.{c, v, r} J R P).obj L
    let I := (coefficientHomResolution.{r, c, v} J R).obj L
    let T := (scalarRestriction.{c, v, max c v r} a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    let A := (StrictScalarHom.tensor.{c, v, r} a).obj B
    let A' := (scalarTensor.{c, v, r} a).obj B
    let ν := totalScalarIso.{c, v, r, w} M a G
    let i := G.tensorIso P hP hp B
    let j := G.tensorIso P hP hp A
    let s := FlatScalarEvaluation.sourceTransport M a (G.exact_computes a ha) (G.nu a) B
    let e := FlatScalarEvaluation.exactRepresentative M a (G.exact_computes a ha) I
    let β := FlatScalarEvaluation.transpose M B P I i d.evaluation
    let q : A ⟶ A' := (singleScalarIso.{c, v, r} a).inv.app B
    let t : (coefficientTotalTensor.{r, c, v} J R).obj (A, P) ⟶
        (coefficientTotalTensor.{r, c, v} J R).obj (A', P) :=
      (coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom q (𝟙 P))
    let eScalar : (coefficientTotalTensor.{r, c, v} J R).obj (A', P) ⟶
        (scalarTensor.{c, v, r} a).obj I := d.scalarEvaluation T
    have hsiso : IsIso s := by
      dsimp only [s, FlatScalarEvaluation.sourceTransport]
      infer_instance
    have hrep (D : CochainComplex (scalarModules J R) ℤ) :
        representative M a ν D =
          (FlatScalarEvaluation.exactRepresentative M a (G.exact_computes a ha) D).hom ≫
            DerivedCategory.Q.map (ν.inv.app D) := by
      simp only [representative, FlatScalarEvaluation.exactRepresentative, Iso.trans_hom,
        Functor.mapIso_hom, asIso_hom, Category.assoc]
      rfl
    have hs : s ≫ representative M a ν B = DerivedCategory.Q.map q := by
      rw [hrep]
      dsimp only [s, FlatScalarEvaluation.sourceTransport]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, ← DerivedCategory.Q.map_comp]
      simp only [ν, totalScalarIso, Iso.trans_inv, NatTrans.comp_app,
        Iso.hom_inv_id_app_assoc]
      rfl
    have hI : I.IsKInjective := resolution_obj_isKInjective.{c, v, r} L
    have hc := calculation.adjunction_formula a ha P I B hP hp hI (𝟙 _)
    have hevaluate :
      G.evaluate P ((coefficientHomResolution.{r, c, v} J R).obj L)
            ((homFixed.{c, v, r} J R P).obj L) (𝟙 _) = d.evaluation := by
      apply HomologicalComplex.hom_ext
      intro k
      apply ScalarHomTensor.total_pure_hom_ext.{c, v, r}
        ((homFixed.{c, v, r} J R P).obj L) P k
        (((coefficientHomResolution.{r, c, v} J R).obj L).X k)
      intro n p h V f x
      have he := G.evaluate_pure P ((coefficientHomResolution.{r, c, v} J R).obj L)
        ((homFixed.{c, v, r} J R P).obj L) (𝟙 _) n p k h (by omega) V f x
      dsimp only [HomologicalComplex.id_f, SheafOfModules.id_val,
        PresheafOfModules.id_app, ModuleCat.id_apply] at he
      change _ = StrictScalarHom.evaluate P _ n p k (by omega) V f x at he
      refine he.trans ?_
      simpa only [StrictScalarHom.evaluate, homValue,
        HomologicalComplex.id_f, SheafOfModules.id_val,
        PresheafOfModules.id_app, ModuleCat.id_apply, id_eq] using
        (hEvaluationPure n p k h (by omega) V f x).symm
    rw [hevaluate] at hc
    have he := scalarEvaluation_transport M a G P
      ((coefficientHomResolution.{r, c, v} J R).obj L)
      eScalar
      (hScalarPure T)
    have ht := hTransposeDerived
      T
    have hn := G.tensorIso_natural P A' A hP hp q
    conv at hn =>
      lhs
      rw [← htensor A']
    have hprod : Prod.mkHom q (𝟙 P) ≫
        Prod.mkHom ((singleScalarIso.{c, v, r} a).hom.app B) (𝟙 P) = 𝟙 (A, P) := by
      apply CategoryTheory.Prod.hom_ext
      · exact (singleScalarIso.{c, v, r} a).inv_hom_id_app B
      · exact Category.id_comp (𝟙 P)
    have hchain := conjugate_inverse
      ((coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom ((singleScalarIso.{c, v, r} a).hom.app B) (𝟙 P))) t (ν.app I)
      eScalar
      (G.scalarEvaluate a P I B (𝟙 _)) he (by
        dsimp only [t]
        rw [← Functor.map_comp, hprod, Functor.map_id])
    change G.scalarEvaluate a P I B (𝟙 _) ≫ ν.inv.app I =
      t ≫ eScalar at hchain
    let g := (scalarDerivedRestriction a).map ((M.scalar a).derived.map β) ≫
      restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
    dsimp only [FlatScalarEvaluation.adjunctionEvaluation] at hc
    change j.hom ≫ (M.closed R).tensor.map (Prod.mkHom s (𝟙 _)) ≫
      ((M.closed R).transpose _ _ _).symm g ≫ e.hom = _ at hc
    have hchain' : DerivedCategory.Q.map (G.scalarEvaluate a P I B (𝟙 _)) ≫
        DerivedCategory.Q.map (ν.inv.app I) =
      DerivedCategory.Q.map t ≫ DerivedCategory.Q.map eScalar := by
      exact map_composition_equality DerivedCategory.Q hchain
    have hr := resolved_diagram (M.closed R) s (representative M a ν B)
      (DerivedCategory.Q.map q) g e.hom (DerivedCategory.Q.map (ν.inv.app I))
      (DerivedCategory.Q.map (numerator.{c, v, r} a P L) ≫
        (coefficientHomResolutionIso.{r, c, v, w} J R P ((scalarTensor.{c, v, r} a).obj I)).inv)
      j _ (d.tensorIso A') (DerivedCategory.Q.map t)
      (DerivedCategory.Q.map (G.scalarEvaluate a P I B (𝟙 _)))
      (DerivedCategory.Q.map eScalar) hs hc hn ht hchain'
    conv at hr =>
      lhs
      rw [← hrep I]
    simpa only [g, β, Category.assoc] using hr
  rw [heval] at hc
  let H := fixedDerivedHom.{c, v, r, w} (J := J) P
  let F := (M.scalar a).derived
  let U := scalarDerivedRestriction a
  let I := coefficientHomResolution.{r, c, v} J R
  let B := (homFixed.{c, v, r} J R P).obj L
  let ν := totalScalarIso.{c, v, r, w} M a G
  let e := DerivedCategory.Q.map ((resolutionUnit.{c, v, r} J R).app L)
  let i := coefficientHomResolutionIso.{r, c, v, w} J R P L
  let j := coefficientHomResolutionIso.{r, c, v, w} J R P ((scalarTensor.{c, v, r} a).obj L)
  let k := coefficientHomResolutionIso.{r, c, v, w} J R P ((scalarTensor.{c, v, r} a).obj (I.obj L))
  have hn := restrictedComparison_natural M μ α coherence a
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj (I.obj L)) (𝟙 _) e
  simp only [op_id] at hn
  change U.map (F.map (H.map e)) ≫ restrictedComparison M μ α a _ _ =
    restrictedComparison M μ α a _ _ ≫ H.map (U.map (F.map e)) at hn
  have hr := representative_natural M a ν ((resolutionUnit.{c, v, r} J R).app L)
  change U.map (F.map e) ≫ representative M a ν (I.obj L) =
    representative M a ν L ≫ DerivedCategory.Q.map
      ((scalarTensor.{c, v, r} a).map ((resolutionUnit.{c, v, r} J R).app L)) at hr
  have hh := homResolution_natural.{c, v, r, w} (J := J) P
    ((scalarTensor.{c, v, r} a).map ((resolutionUnit.{c, v, r} J R).app L))
  change H.map (DerivedCategory.Q.map
      ((scalarTensor.{c, v, r} a).map ((resolutionUnit.{c, v, r} J R).app L))) ≫ k.hom =
    j.hom ≫ DerivedCategory.Q.map (denominator.{c, v, r} a P L) at hh
  change U.map (F.map (i.inv ≫ H.map e)) ≫
      restrictedComparison M μ α a _ _ ≫ H.map (representative M a ν (I.obj L)) =
    representative M a ν B ≫ DerivedCategory.Q.map (numerator.{c, v, r} a P L) ≫ k.inv at hc
  have hi : U.map (F.map i.hom) ≫ U.map (F.map (i.inv ≫ H.map e)) =
      U.map (F.map (H.map e)) := by
    rw [← U.map_comp, ← F.map_comp, Iso.hom_inv_id_assoc]
  have hm := congrArg H.map hr
  rw [H.map_comp, H.map_comp] at hm
  have heq := roof_diagram (U.map (F.map i.hom))
    (U.map (F.map (i.inv ≫ H.map e))) (U.map (F.map (H.map e)))
    (restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L))
    (restrictedComparison M μ α a (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj (I.obj L)))
    (H.map (U.map (F.map e))) (H.map (representative M a ν L))
    (H.map (representative M a ν (I.obj L)))
    (H.map (DerivedCategory.Q.map ((scalarTensor.{c, v, r} a).map
      ((resolutionUnit.{c, v, r} J R).app L)))) j.hom k
    (DerivedCategory.Q.map (denominator.{c, v, r} a P L)) (representative M a ν B)
    (DerivedCategory.Q.map (numerator.{c, v, r} a P L)) hi hn hm hh hc
  dsimp only [H, fixedDerivedHom, U, F, i, j, k, ν, B, I] at heq
  change restrictedComparison M μ α a _ _ ≫
      ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
          (representative M a (totalScalarIso.{c, v, r, w} M a G) L)) ≫
        (coefficientHomResolutionIso.{r, c, v, w} J R P
          ((scalarTensor.{c, v, r} a).obj L)).hom) ≫ _ = _
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simpa only [sourceMap, Category.assoc] using heq
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Flat scalar comparison is precisely the evaluation-normalized strict resolution roof.
All presentations are those of the dependency nodes, and no finite basis, colimit
continuity, or bound on either complex is assumed.

Source: Stacks Project, sites-cohomology.tex, Tags 08J9 and 0A95; sites-modules.tex,
Tag 03CZ; blueprint main-20261015, lem-sfb-dc-hom-preserves.proof.md, final paragraph,
as refined by the six proof steps of the DAG node
(blueprint: lem-sfb-hom-flat-evaluation-roof).

Proof:
1. Exact extension commutes with cohomology and preserves quasi-isomorphisms.
   Resolve an arbitrary complex by a flat-term K-flat complex. The universal derived
   counit and preservation of this resolution make its exact-extension representative
   comparison invertible. Apply this to E eta_C. Naturality and two-out-of-three show
   I_R(E eta_C) is a quasi-isomorphism between K-injectives. Hom invariance proves v_S
   is a quasi-isomorphism (Tags 010N, 06YY, 0A95).
2. Set J_C = I_R(C) and B = Hom(P,J_C). The one-K-flat chain-transpose lemma computes
   evaluation by B tensor P to J_C followed by the inverse localized eta_C. It also
   applies to the arbitrary complex S tensor B; this complex need not be K-flat.
3. The scalar chain identification gives h((s tensor f) tensor p) = s tensor f(p).
   The strict numerator has uncurry eta_(S tensor J_C) composed with h, by its fixed
   pure-tensor and Hom-product-projection normalization. Its derived transpose is [h].
4. Resolve B by a flat-term K-flat T. On T,P the normalized scalar tensor comparison
   is the actual chain tensor identification. Tensoring with P and applying exact E
   preserve the resolution quasi-isomorphisms. Descent therefore gives the same h
   on S tensor B, without asserting that arbitrary tensor computes derived tensor.
5. The normalized scalar adjunction makes the transpose of Theta U(c) equal to
   [E eta_C] inverse composed with [h]. Postcomposition by [v_S] cancels this inverse.
   The transpose becomes [h], equal to the numerator's transpose by step 3.
   Injectivity of the closed transpose gives the equation; inversion of [v_S] gives
   the equivalent roof formula.
6. Evaluation commutes with precomposition in P and postcomposition in C. Naturality
   of the fixed resolution unit, scalar tensor square and scalar adjunction gives
   these equations on representatives and their inverse quasi-isomorphisms, hence
   on all derived morphisms. The same calculation with successive scalar units and
   the unit-normalized scalar composition isomorphisms gives coefficient compatibility.
   Both paths of a compatible coefficient square have the same evaluation transpose.
   Identity coefficients are included. No finite freeness, continuity or bound occurs. -/
theorem evaluationRoof : Nonempty (EvaluationRoof M μ α) := by
  obtain ⟨E⟩ := FlatScalarEvaluation.model_exists.{c, v, r, w} M μ α
  refine ⟨{ tensorIso := fun a ↦ totalScalarIso.{c, v, r, w} M a E.representatives
            tensorIso_normalized := totalScalarIso_pure M E.representatives
            exact_computes := E.representatives.exact_computes
            denominator_quasiIso := denominator_quasiIso_proof M E.representatives
            equation := roof_equation M μ α E.representatives E.calculation E.coherence
            roof := ?_
            naturality := restrictedComparison_natural M μ α E.coherence
            coefficients := ?_ }⟩
  · intro R S a ha P L hP hp hv
    let := hv
    have : IsIso (DerivedCategory.Q.map (denominator.{c, v, r} a P L)) :=
      inferInstance
    have he := roof_equation M μ α E.representatives E.calculation E.coherence a ha P L hP hp
    apply (cancel_mono (DerivedCategory.Q.map (denominator.{c, v, r} a P L))).mp
    dsimp only [denominatorInverse]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact he
  · intro R S T a b K L
    have hc := E.coherence.composition a b K L
    change (M.scalar b).derived.map (comparison M μ a K L) ≫
      comparison M μ b ((M.scalar a).derived.obj K) ((M.scalar a).derived.obj L) ≫ _ =
      (scalarHomExtensionComp M a b).hom.app _ ≫ comparison M μ (a ≫ b) K L at hc
    symm
    rw [hc, Iso.inv_hom_id_app_assoc]

end CategoryTheory.SfbFlatHom
