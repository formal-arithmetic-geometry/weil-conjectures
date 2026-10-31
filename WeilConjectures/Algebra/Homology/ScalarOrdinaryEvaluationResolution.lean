/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ScalarOrdinaryEvaluationModel
public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
import all WeilConjectures.Algebra.Homology.ScalarOrdinaryEvaluationCoefficientSquare
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Algebra.Homology.ScalarHomTensorCoherence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Flat scalar evaluation on an arbitrary first complex

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 08J9 and 06YP;
the one-K-flat-factor scalar evaluation refinement recorded in the DAG, rather
than a verbatim assertion of these tags
(blueprint: lem-sfb-ordinary-scalar-evaluation-resolution).

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


private theorem tensor_quasiIso {R : Sheaf J CommRingCat.{max c v r}}
    (P : StrictScalarHom.Complex.{c, v, r} R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    {X Y : StrictScalarHom.Complex.{c, v, r} R} (t : X ⟶ Y) (ht : QuasiIso t) :
    QuasiIso ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom t (𝟙 P))) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have hh := kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP t ht
  delta coefficientTotalTensor
  change QuasiIso
    (((MonoidalCategory.curriedTensor (scalarModules J R)).map₂CochainComplex.map t).app P ≫
      ((MonoidalCategory.curriedTensor (scalarModules J R)).map₂CochainComplex.obj Y).map (𝟙 P))
  rw [Functor.map_id, Category.comp_id]
  exact hh

/-- Exact scalar extension and a K-flat right factor preserve a resolution,
and scalar evaluation commutes with its resolution map.
Source: Stacks 06YP, 07A4 and 08J9, arbitrary-first-factor resolution argument
(blueprint: lem-sfb-ordinary-scalar-evaluation-resolution).

Proof: exact additive extension preserves homology. Tensoring with P preserves
quasi-isomorphisms by K-flatness. The normalized nu identifies strict scalar
tensor with restricted extension, so it preserves the resolution map as well.
For the evaluation equality, both routes on (s tensor x) tensor p are
s tensor b(t(x))(p); sheafified tensor generation proves equality. -/
theorem resolution (O : Scalars.{c, v, r} (J := J))
    (E : RepresentativeData.{c, v, r} (J := J) O)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (ha : PreservesFiniteLimits (O.E a))
    (P I D V : StrictScalarHom.Complex.{c, v, r} R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (b : D ⟶ homComplex (R := R) P I) (t : V ⟶ D) (ht : QuasiIso t) :
    QuasiIso ((extension O a).map t) ∧
    QuasiIso ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom t (𝟙 P))) ∧
    QuasiIso ((extension O a).map
      ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom t (𝟙 P)))) ∧
    QuasiIso ((coefficientTotalTensor.{r, c, v} J R).map
      (Prod.mkHom ((StrictScalarHom.tensor.{c, v, r} a).map t) (𝟙 P))) ∧
    (coefficientTotalTensor.{r, c, v} J R).map
      (Prod.mkHom ((StrictScalarHom.tensor.{c, v, r} a).map t) (𝟙 P)) ≫
      E.scalarEvaluate a P I D b = E.scalarEvaluate a P I V (t ≫ b) := by
  let (T : Sheaf J CommRingCat.{max c v r}) :
      HasDerivedCategory (scalarModules J T) := HasDerivedCategory.standard _
  let := ha
  let := O.additive a
  let := (O.adj a).isLeftAdjoint
  let := ht
  have hEt : QuasiIso ((extension O a).map t) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology t (O.E a)
  let := hEt
  have htP := tensor_quasiIso.{c, v, r} (J := J) P hP t ht
  let := htP
  have hEtP : QuasiIso ((extension O a).map
      ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom t (𝟙 P)))) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ (O.E a)
  have hSt : QuasiIso ((StrictScalarHom.tensor.{c, v, r} a).map t) := by
    have hnat := (E.nu a).hom.naturality t
    have : QuasiIso (((StrictScalarHom.tensor.{c, v, r} a).map t) ≫
        (E.nu a).hom.app D) := by
      rw [hnat]
      change QuasiIso ((E.nu a).hom.app V ≫
        ((scalarRestriction a).mapHomologicalComplex (.up ℤ)).map ((extension O a).map t))
      infer_instance
    exact (quasiIso_iff_comp_right
      ((StrictScalarHom.tensor.{c, v, r} a).map t) ((E.nu a).hom.app D)).mp this
  refine ⟨hEt, htP, hEtP,
    tensor_quasiIso.{c, v, r} (J := J) P hP _ hSt, ?_⟩
  apply scalar_tensor_ext a V P
  intro n i k h W s x p
  change ((E.scalarEvaluate a P I D b).f k).val.app W
    ((((coefficientTotalTensor.{r, c, v} J R).map
      (Prod.mkHom ((StrictScalarHom.tensor.{c, v, r} a).map t) (𝟙 P))).f k).val.app W
      (coefficientTensorGenerator.{r, c, v} J R _ P n i k h W
        (StrictScalarHom.tensorSection.{c, v, r} a V n W s x) p)) = _
  rw [ScalarHomTensor.tensor_generator_map, StrictScalarHom.tensor_map_section]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  rw [E.scalarEvaluate_pure a P I D b n i k h (by omega),
    E.scalarEvaluate_pure a P I V (t ≫ b) n i k h (by omega)]
  rfl

end CategoryTheory.ScalarOrdinaryEvaluation
