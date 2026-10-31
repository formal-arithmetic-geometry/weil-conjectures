/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ScalarOrdinaryEvaluationModel
import all WeilConjectures.Algebra.Homology.ScalarOrdinaryEvaluationModel
import all WeilConjectures.Algebra.Homology.StrictScalarHomChain
import all WeilConjectures.Algebra.Homology.ScalarHomTensorCoherence
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
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

/-! # Flat scalar evaluation on an arbitrary first complex

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 08J9 and 06YP;
the one-K-flat-factor scalar evaluation refinement recorded in the DAG, rather
than a verbatim assertion of these tags
(blueprint: lem-sfb-ordinary-scalar-evaluation-square).

All tensors, Hom products, sections and localization functors below are the
recorded constructions. The data asserted to exist are fixed by generator
formulas and the K-flat normalization; no representative is chosen arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
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
  CoefficientClosedStructure.tensor
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors

attribute [local irreducible] homComplex homComplexπ
  RingedDerivedNative.chainEquiv

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  scalarPairComplexComparison CoefficientTensorModels.iso
  SheafOfModules.monoidalCategory homComplexFunctor


namespace CategoryTheory.ScalarOrdinaryEvaluation

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]


private theorem scalar_tensor_ext {R S : Sheaf J CommRingCat.{max c v r}}
    (a : R ⟶ S) (D P I : StrictScalarHom.Complex.{c, v, r} R)
    (f g : (coefficientTotalTensor.{r, c, v} J R).obj
      ((StrictScalarHom.tensor.{c, v, r} a).obj D, P) ⟶ I)
    (hfg : ∀ (n i k : ℤ) (h : n + i = k) (V : Cᵒᵖ)
      (s : S.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V),
      (f.f k).val.app V (coefficientTensorGenerator.{r, c, v} J R
          ((StrictScalarHom.tensor.{c, v, r} a).obj D) P n i k h V
          (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p) =
        (g.f k).val.app V (coefficientTensorGenerator.{r, c, v} J R
          ((StrictScalarHom.tensor.{c, v, r} a).obj D) P n i k h V
          (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p)) : f = g := by
  let (R : Sheaf J CommRingCat.{max c v r}) :
      HasDerivedCategory (scalarModules J R) := HasDerivedCategory.standard _
  let e := RingedDerivedNative.chainEquiv.{c, v, r} J R
    ((StrictScalarHom.tensor.{c, v, r} a).obj D) P I
  apply e.injective
  ext n : 1
  apply StrictScalarHom.tensorModuleHom_ext.{c, v, r} a D P I n
  intro i k h V s x p
  have hf := RingedDerivedNative.chainEquiv_symm_pure.{c, v, r} J R
    ((StrictScalarHom.tensor.{c, v, r} a).obj D) P I (e f)
    n i k (by omega) h V (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p
  have hg := RingedDerivedNative.chainEquiv_symm_pure.{c, v, r} J R
    ((StrictScalarHom.tensor.{c, v, r} a).obj D) P I (e g)
    n i k (by omega) h V (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p
  change (((e.symm (e f)).f k).val.app V _) = _ at hf
  change (((e.symm (e g)).f k).val.app V _) = _ at hg
  rw [Equiv.symm_apply_apply] at hf hg
  exact hf.symm.trans ((hfg n i k (by omega) V s x p).trans hg)

private theorem presentation_inv_pure (O : Scalars.{c, v, r} (J := J)) (B : Presentation.{c, v, r}
  (J := J) O)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) :
    ((((B.chainIso a).inv.app D).f n).val.app V)
      (extensionSection.{c, v, r} (J := J) O a D n V s x) =
        (B.chainData a).extension.section D n V s x := by
  rw [← B.chainIso_pure a D n V s x]
  exact congrArg (fun f ↦ (f.f n).val.app V
    ((B.chainData a).extension.section D n V s x)) ((B.chainIso a).app D).hom_inv_id

private theorem presentation_hom_pure (O : Scalars.{c, v, r} (J := J)) (B : Presentation.{c, v, r}
  (J := J) O)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (b : D ⟶ homComplex (R := R) P I)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (x : (D.X n).val.obj V) (p : (P.X i).val.obj V) :
    StrictScalarHom.evaluate.{c, v, r}
      ((B.chainData a).extension.complex.obj P)
      ((B.chainData a).extension.complex.obj I) n i k h V
      ((((B.chainData a).extension.complex.map b ≫
        (B.chainData a).homComparison P I).f n).val.app V
        ((B.chainData a).extension.section D n V 1 x))
      ((B.chainData a).extension.section P i V 1 p) =
      (B.chainData a).extension.section I k V 1
        (StrictScalarHom.evaluate.{c, v, r} P I n i k h V ((b.f n).val.app V x) p) := by
  change StrictScalarHom.evaluate _ _ n i k h V
    ((((B.chainData a).homComparison P I).f n).val.app V
      ((((B.chainData a).extension.complex.map b).f n).val.app V
        ((B.chainData a).extension.section D n V 1 x))) _ = _
  rw [StrictScalarHom.extension_map_section_generic]
  exact StrictScalarHom.dataSigma_unit (B.chainData a) P I _ (𝟙 _) n i k h V
    ((b.f n).val.app V x) p

private theorem presentation_inv_unit (O : Scalars.{c, v, r} (J := J)) (B : Presentation.{c, v, r}
  (J := J) O)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (D : StrictScalarHom.Complex.{c, v, r} R) (n : ℤ) (V : Cᵒᵖ)
    (x : (D.X n).val.obj V) :
    ((((B.chainIso a).inv.app D).f n).val.app V)
      (unitSection.{c, v, r} (J := J) O a (D.X n) V x) =
        (B.chainData a).extension.section D n V 1 x := by
  simpa only [extensionSection, one_smul] using presentation_inv_pure.{c, v, r} (J := J) O B a D n
    V 1 x

set_option maxHeartbeats 800000 in
-- Test both coefficient routes on nested tensor generators.
/-- Evaluation on arbitrary complexes respects compatible coefficient squares.
Source: Stacks 03CY, 03CZ and 0A8X; strict coefficient-square generator calculation
(blueprint: lem-sfb-ordinary-scalar-evaluation-square).

Proof: transpose by the ordinary scalar adjunction and test the resulting maps
on sheafified tensor generators. The tensor comparison sends the unit generator
to the two unit generators. The presentation isomorphisms and the scalar
comparison transport it to d(s) tensor (1 tensor x). Evaluation and Hom
comparison give d(s) tensor (1 tensor b(x)(p)). On the other route, evaluate
first and then use the restriction mate and extension isomorphism; their
specified pure-section equations give the same section. Tensor generation and
injectivity of transposition prove the equality. No derived data are used. -/
theorem coefficient_square (O : Scalars.{c, v, r} (J := J))
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), Tensor O a)
    (E : Evaluation.{c, v, r} (J := J) O) (B : Presentation.{c, v, r} (J := J) O)
    {R S R' S' : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (a : R ⟶ R') (d : S ⟶ S') (φ' : R' ⟶ S')
    (Q : StrictScalarHom.CoefficientSquare.{c, v, r}
      (B.chainData φ) (B.chainData a) (B.chainData d) (B.chainData φ'))
    (hQ : StrictScalarHom.CoefficientCompatibility.{c, v, r} Q)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (b : D ⟶ homComplex (R := R) P I) :
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
        (StrictScalarHom.restriction.{c, v, r} φ').map (Q.extensionIso.hom.app I) := by
  apply (cancel_epi ((B.chainIso a).inv.app _)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply ((chainAdj.{c, v, r} (J := J) O a).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply scalar_tensor_ext φ D P
  intro n i k hn V s x p
  let A := (StrictScalarHom.tensor.{c, v, r} φ).obj D
  let T := coefficientTotalTensor.{r, c, v} J R
  let T' := coefficientTotalTensor.{r, c, v} J R'
  let Da := (B.chainData a).extension
  let b' := Da.complex.map b ≫ (B.chainData a).homComparison P I
  let y := coefficientTensorGenerator.{r, c, v} J R A P n i k hn V
    (StrictScalarHom.tensorSection.{c, v, r} φ D n V s x) p
  change (((B.chainIso φ').inv.app (Da.complex.obj I)).f k).val.app V
    (((E.scalarEvaluate φ' (Da.complex.obj P) (Da.complex.obj I)
      (Da.complex.obj D) b').f k).val.app V
      (((T'.map (Prod.mkHom (Q.tensorComparison D) (𝟙 (Da.complex.obj P)))).f k).val.app V
        (((T'.map (Prod.mkHom ((B.chainIso a).inv.app A)
          ((B.chainIso a).inv.app P))).f k).val.app V
          ((((μ a).complexIso A P).hom.f k).val.app V
            (unitSection.{c, v, r} (J := J) O a ((T.obj (A, P)).X k) V y))))) =
    (((Q.extensionIso.hom.app I).f k).val.app V
      (((Q.restrictionMate.app ((B.chainData φ).extension.complex.obj I)).f k).val.app V
        (((Da.complex.map (E.scalarEvaluate φ P I D b ≫
          (StrictScalarHom.restriction.{c, v, r} φ).map ((B.chainIso φ).inv.app I))).f k).val.app V
          ((((B.chainIso a).inv.app (T.obj (A, P))).f k).val.app V
            (unitSection.{c, v, r} (J := J) O a ((T.obj (A, P)).X k) V y)))))
  dsimp only [y]
  erw [(μ a).generators]
  erw [ScalarHomTensor.tensor_generator_map, presentation_inv_unit,
    presentation_inv_unit]
  erw [ScalarHomTensor.tensor_generator_map, hQ.tensor_pure]
  simp only [map_one, one_mul, HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  erw [E.scalarEvaluate_pure φ' _ _ _ _ n i k hn (by omega),
    presentation_hom_pure, presentation_inv_pure]
  erw [presentation_inv_unit, StrictScalarHom.extension_map_section_generic]
  change _ = (((Q.extensionIso.hom.app I).f k).val.app V
    (((Q.restrictionMate.app ((B.chainData φ).extension.complex.obj I)).f k).val.app V
      (Da.section _ k V 1
        ((((B.chainIso φ).inv.app I).f k).val.app V
          (((E.scalarEvaluate φ P I D b).f k).val.app V
            (coefficientTensorGenerator.{r, c, v} J R A P n i k hn V
              (StrictScalarHom.tensorSection.{c, v, r} φ D n V s x) p))))))
  erw [E.scalarEvaluate_pure φ P I D b n i k hn (by omega),
    presentation_inv_pure]
  erw [Q.restrictionMate_pure, Q.extensionIso_pure]
  simp only [map_one, one_mul]
  rfl



/-- The normalized ordinary evaluation formula identifies the full scalar-unit composite.
Source: Stacks 07A4 and 08J9 (blueprint: lem-sfb-ordinary-scalar-evaluation-square).

Proof: test on (s tensor x) tensor p. Nu sends the first factor to s times the
unit of x. The unit tensor map inserts the unit of p. Inverse tensor comparison
returns s tensor (x tensor p); extension of evaluation gives s tensor b(x)(p),
which is exactly scalar evaluation. Tensor generation proves the equality. -/
private theorem evaluation_composite (O : Scalars.{c, v, r} (J := J))
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), Tensor O a)
    (E : RepresentativeData.{c, v, r} (J := J) O)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P I D : StrictScalarHom.Complex.{c, v, r} R) (b : D ⟶ homComplex (R := R) P I) :
    (coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom ((E.nu a).hom.app D) (𝟙 P)) ≫
      E.chainUnitTensor a D P ≫
      (StrictScalarHom.restriction.{c, v, r} a).map ((μ a).complexIso D P).inv ≫
      (StrictScalarHom.restriction.{c, v, r} a).map
        ((extension.{c, v, r} (J := J) O a).map (E.evaluate P I D b)) = E.scalarEvaluate a P I
          D b := by
  apply scalar_tensor_ext a D P
  intro n i k h V s x p
  change (((extension.{c, v, r} (J := J) O a).map (E.evaluate P I D b)).f k).val.app V
    ((((μ a).complexIso D P).inv.f k).val.app V
      (((E.chainUnitTensor a D P).f k).val.app V
        ((((coefficientTotalTensor.{r, c, v} J R).map
          (Prod.mkHom ((E.nu a).hom.app D) (𝟙 P))).f k).val.app V
          (coefficientTensorGenerator.{r, c, v} J R _ P n i k h V
            (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p)))) = _
  rw [ScalarHomTensor.tensor_generator_map, E.nu_pure]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  erw [E.chainUnitTensor_pure, tensorComparison_inv_pure O μ, extensionSection_map O,
    E.evaluate_pure P I D b n i k h (by omega),
    E.scalarEvaluate_pure a P I D b n i k h (by omega)]


end CategoryTheory.ScalarOrdinaryEvaluation
